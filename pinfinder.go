// pinfinder魔改版 by Lee

package main

import (
	"bufio"
	"bytes"
	"crypto/sha1"
	"encoding/base64"
	"errors"
	"flag"
	"fmt"
	"html/template"
	"io"
	"os"
	"os/user"
	"path"
	"path/filepath"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/DHowett/go-plist"
	"github.com/gwatts/ios/keychain"
	"github.com/howeyc/gopass"
	"golang.org/x/crypto/pbkdf2"
)

const (
	maxPIN                = 10000
	version               = "1.7.1"
	restrictionsPlistName = "398bc9c2aeeab4cb0c12ada0f52eea12cf14f40b"

	msgIsEncrypted        = "backup is encrypted"
	msgEncryptionDisabled = "encrypted backups not supported"
	msgNoPasscode         = "none"
	msgIncorrectPassword  = "incorrect encryption password"
	msgNoPassword         = "need encryption password"
	msgKeychainLoadFailed = "failed to read keychain"
	msgEncryptedNeeded    = "need encrypted backup"
)

var (
	noPause     = flag.Bool("nopause", false, "Set to true to prevent the program pausing for input on completion")
	showLicense = flag.Bool("license", false, "Display license information")
	diag        = flag.Bool("diag", false, "Generate a diagnostic pinfinder-debug.zip file")
)

func isDir(p string) bool {
	s, err := os.Stat(p)
	if err != nil {
		return false
	}
	return s.IsDir()
}

func dumpFile(fn string) {
	if f, err := os.Open(fn); err != nil {
		fmt.Printf("Failed to open %s: %s\n", fn, err)
	} else {
		defer f.Close()
		io.Copy(os.Stdout, f)
	}
}

func appendIfDir(dirs []string, dir string) []string {
	if isDir(dir) {
		return append(dirs, dir)
	}
	return dirs
}

// figure out where iTunes keeps its backups on the current OS
func findSyncDirs() (dirs []string, err error) {

	usr, err := user.Current()
	if err != nil {
		return nil, fmt.Errorf("failed to get information about current user: %s", err)
	}

	switch runtime.GOOS {
	case "darwin":
		dir := filepath.Join(usr.HomeDir, "Library", "Application Support", "MobileSync", "Backup")
		dirs = appendIfDir(dirs, dir)

	case "windows":
		// this seems to be correct for all versions of Windows.. Tested on XP and Windows 8
		dir := filepath.Join(os.Getenv("APPDATA"), "Apple Computer", "MobileSync", "Backup")
		dirs = appendIfDir(dirs, dir)

		dir = filepath.Join(os.Getenv("USERPROFILE"), "Apple", "MobileSync", "Backup")
		dirs = appendIfDir(dirs, dir)

	default:
		return nil, errors.New("could not detect backup directory for this operating system; pass explicitly")
	}
	return dirs, nil
}

func parsePlist(fn string, target interface{}) error {
	f, err := os.Open(fn)
	if err != nil {
		return err
	}

	return plist.NewDecoder(f).Decode(target)
}

func fileExists(fn string) bool {
	fi, err := os.Stat(fn)
	if err != nil {
		return false
	}
	return fi.Mode().IsRegular()
}

var backupInfoTpl = template.Must(template.New("backup").Parse(`
Path: {{.Path}}
Status: {{.Status}}
RestrictionPath: {{.RestrictionsPath}}
IsEncrypted: {{.Manifest.IsEncrypted}}

Key: {{.Restrictions.Key}}
Salt: {{.Restrictions.Salt}}

LastBackup: {{.Info.LastBackup}}
DisplayName: {{.Info.DisplayName}}
ProductName: {{.Info.ProductName}}
ProductType: {{.Info.ProductType}}
ProductVersion: {{.Info.ProductVersion}}
`))

type backup struct {
	Path             string
	Status           string
	RestrictionsPath string
	UsesScreenTime   bool
	Info             struct {
		LastBackup     time.Time `plist:"Last Backup Date"`
		DisplayName    string    `plist:"Display Name"`
		ProductName    string    `plist:"Product Name"`
		ProductType    string    `plist:"Product Type"`
		ProductVersion string    `plist:"Product Version"`
	}
	Manifest struct {
		IsEncrypted interface{} `plist:"IsEncrypted"`
	}
	Restrictions struct {
		Key  []byte `plist:"RestrictionsPasswordKey"`
		Salt []byte `plist:"RestrictionsPasswordSalt"`
	}
	Keychain *keychain.Keychain
}

func (b *backup) debugInfo() string {
	var buf bytes.Buffer
	backupInfoTpl.Execute(&buf, b)
	return buf.String()
}

func (b *backup) isEncrypted() bool {
	switch v := b.Manifest.IsEncrypted.(type) {
	case int:
		return v != 0
	case uint64:
		return v != 0
	case bool:
		return v
	case nil:
		return false
	default:
		return false
	}
}

func (b *backup) isIOS12() bool {
	return majorVersion(b.Info.ProductVersion) >= 12
}

type backups struct {
	encrypted bool
	backups   []*backup
}

func (b backups) Len() int { return len(b.backups) }
func (b backups) Less(i, j int) bool {
	return b.backups[i].Info.LastBackup.Before(b.backups[j].Info.LastBackup)
}
func (b backups) Swap(i, j int) { b.backups[i], b.backups[j] = b.backups[j], b.backups[i] }

func (b *backups) loadBackups(syncDir string, pwd string) error {
	// loop over all directories and see whether they contain an Info.plist
	d, err := os.Open(syncDir)
	if err != nil {
		if err := isBadMacPerms(err); err != nil {
			return err
		}
		return fmt.Errorf("failed to open directory %q: %s", syncDir, err)
	}
	defer d.Close()
	fl, err := d.Readdir(-1)
	if err != nil {
		return fmt.Errorf("failed to read directory %q: %s", syncDir, err)
	}
	for _, fi := range fl {
		if !fi.Mode().IsDir() {
			continue
		}
		path := filepath.Join(syncDir, fi.Name())
		if backup, _ := loadBackup(path, pwd); backup != nil {
			b.backups = append(b.backups, backup)
			if backup.isEncrypted() {
				b.encrypted = true
			}
		}
	}
	sort.Sort(sort.Reverse(b))
	return nil
}

func majorVersion(v string) int {
	parts := strings.Split(v, ".")
	if len(parts) < 1 {
		return 0
	}
	maj, err := strconv.Atoi(parts[0])
	if err != nil {
		return 0
	}
	return maj
}

func loadBackup(backupDir string, pwd string) (*backup, error) {
	var b backup

	if err := parsePlist(filepath.Join(backupDir, "Info.plist"), &b.Info); err != nil {
		return nil, err // no Info.plist == invalid backup dir
	}

	if err := parsePlist(filepath.Join(backupDir, "Manifest.plist"), &b.Manifest); err != nil {
		return nil, err // no Manifest.plist == invaild backup dir
	}

	b.Path = backupDir

	switch {
	case b.isIOS12():
		if !b.isEncrypted() {
			b.Status = msgEncryptedNeeded
			return &b, nil
		}
		decrypt(backupDir, &b, pwd)

	default:
		b.RestrictionsPath = filepath.Join(backupDir, restrictionsPlistName)
		if _, err := os.Stat(b.RestrictionsPath); err != nil {
			// iOS 10 moved backup files into sub-folders beginning with
			// the first 2 letters of the filename.
			b.RestrictionsPath = filepath.Join(backupDir, restrictionsPlistName[:2], restrictionsPlistName)
		}

		if !fileExists(b.RestrictionsPath) {
			b.Status = msgNoPasscode
			return &b, nil
		}
		if b.isEncrypted() {
			decrypt(backupDir, &b, pwd)
			return &b, nil
		}
		if err := parsePlist(b.RestrictionsPath, &b.Restrictions); err != nil {
			b.Status = err.Error()
		}
	}

	return &b, nil
}

var prompted bool
var cachepw string

func getpw() string {
	if prompted {
		return cachepw
	}
	prompted = true
	//fmt.Println("\nSome backups are encrypted; passcode recovery requires the")
	//fmt.Println("encryption password used with iTunes.  Press return to skip.")
	fmt.Print("\n请输入你的iTunes备份密码: ")
	pw, _ := gopass.GetPasswdMasked()
	fmt.Println("")
	cachepw = string(pw)
	if cachepw != "" {
		fmt.Println("正在解密iTunes备份中...")
	}
	return cachepw
}

type swg struct{ sync.WaitGroup }

func (wg *swg) WaitChan() chan struct{} {
	c := make(chan struct{}, 1)
	go func() {
		wg.Wait()
		c <- struct{}{}
	}()
	return c
}

// use all available cores to brute force the PIN
func findPIN(key, salt []byte) (string, error) {
	found := make(chan string)
	var wg swg
	var start, end int

	perCPU := maxPIN / runtime.NumCPU()

	for i := 0; i < runtime.NumCPU(); i++ {
		wg.Add(1)
		if i == runtime.NumCPU()-1 {
			end = maxPIN
		} else {
			end += perCPU
		}

		go func(start, end int) {
			for j := start; j < end; j++ {
				guess := fmt.Sprintf("%04d", j)
				k := pbkdf2.Key([]byte(guess), salt, 1000, len(key), sha1.New)
				if bytes.Equal(k, key) {
					found <- guess
					return
				}
			}
			wg.Done()
		}(start, end)

		start += perCPU
	}

	select {
	case <-wg.WaitChan():
		return "", errors.New("failed to calculate PIN")
	case pin := <-found:
		return pin, nil
	}
}

func findPINFromKeychain(b *backup) (string, error) {
	items := b.Keychain.General.FindByKeyMatch(keychain.KService, "ParentalControls")
	//items := b.Keychain.General.FindByKeyMatch(keychain.KService, "GRDBKeyChainService")

	//循环打印 KeychainItemList
	if len(items) == 0 {
		return "", fmt.Errorf("none")
	}
	code, ok := items[0][keychain.KData].([]byte)
	if !ok {
		return "", fmt.Errorf(msgNoPasscode)
	}
	return string(code), nil
}

func exit(status int, addUsage bool, errfmt string, a ...interface{}) {
	if errfmt != "" {
		fmt.Fprintf(os.Stderr, errfmt+"\n", a...)
	}
	if addUsage {
		usage()
	}
	if !*noPause {
		fmt.Printf("按任意按键退出!")
		bufio.NewReader(os.Stdin).ReadBytes('\n')
	}
	os.Exit(status)
}

var badMacPerms = errors.New("mac full disk access required")

func isBadMacPerms(err error) error {
	if runtime.GOOS != "darwin" {
		return nil
	}
	perr, ok := err.(*os.PathError)
	if !ok || perr.Err != syscall.EPERM {
		return nil
	}
	return badMacPerms
}

func exitBadMacPerms() {
	fmt.Fprintln(os.Stderr, "\nOperation not permitted: Full Disk Access Required")
	fmt.Fprintln(os.Stderr, "Please grant \"Full Disk Access\" to Terminal to run pinfinder")
	fmt.Fprintln(os.Stderr, "See https://pinfinder.net/mac.html for help")
	os.Exit(130)
}

func usage() {
	fmt.Fprintln(os.Stderr, "Usage:", path.Base(os.Args[0]), " [flags] [<path to latest iTunes backup directory>]")
	flag.PrintDefaults()
}

func init() {
	flag.Usage = usage
}

func displayLicense() {
	fmt.Println("LICENSE INFORMATION")
	fmt.Println("-------------------")
	fmt.Println()
	for _, fn := range licenses.Filenames() {
		fmt.Println(fn)
		fmt.Println()
		f, _ := licenses.Open(fn)
		io.Copy(os.Stdout, f)
		fmt.Println()
		fmt.Println()
	}
	fmt.Println()
}

func generateReport(f io.Writer, includeDirName bool, allBackups *backups) {
	if includeDirName {
		fmt.Fprintf(f, "%-70s", "BACKUP DIR")
	}

	//fmt.Fprintf(f, "%-35.35s  %-7.7s  %-25s  %s\n", "设备名", "IOS版本", "iTunes最后备份时间", "屏幕限制时间密码")
	failed := make([]*backup, 0)

	for _, b := range allBackups.backups {
		info := b.Info
		if includeDirName {
			fmt.Fprintf(f, "%-70s", filepath.Base(b.Path))
		}

		//fmt.Fprintf(f, "%-35.35s  %-7.7s %s  ",
		//	info.DisplayName,
		//	info.ProductVersion,
		//info.LastBackup.In(time.Local).Format("Jan _2, 2006 03:04 PM MST") //)

		fmt.Println("---------------------------------------------------------------------")
		fmt.Println("iOS设备名:", info.DisplayName)
		fmt.Println("iOS系统版本:", info.ProductVersion)
		fmt.Println("iTunes最后备份时间:", info.LastBackup.In(time.Local).Format("Jan _2, 2006 03:04 PM MST"))

		if b.UsesScreenTime {
			pin, err := findPINFromKeychain(b)
			if err != nil {
				fmt.Fprintln(f, err.Error())
			} else {
				//fmt.Fprintln(f, pin)
				fmt.Println("屏幕限制时间密码:", pin)
			}

		} else if len(b.Restrictions.Key) > 0 {
			pin, err := findPIN(b.Restrictions.Key, b.Restrictions.Salt)
			if err != nil {
				fmt.Fprintln(f, "Failed to find passcode")
				failed = append(failed, b)
			} else {
				fmt.Fprintln(f, pin)
			}
		} else {
			fmt.Fprintln(f, b.Status)
		}
	}
	fmt.Println("---------------------------------------------------------------------")

	fmt.Fprintln(f)
	for _, b := range failed {
		fmt.Fprintf(f, "Failed to find PIN for backup %s\nPlease file a bug report at https://github.com/gwatts/pinfinder/issues\n", b.Path)
		fmt.Fprintf(f, "%-20s: %s\n", "Product Name", b.Info.ProductName)
		fmt.Fprintf(f, "%-20s: %s\n", "Product Type", b.Info.ProductType)
		fmt.Fprintf(f, "%-20s: %s\n", "Product Version", b.Info.ProductVersion)
		fmt.Fprintf(f, "%-20s: %s\n", "Salt", base64.StdEncoding.EncodeToString(b.Restrictions.Salt))
		fmt.Fprintf(f, "%-20s: %s\n", "Key", base64.StdEncoding.EncodeToString(b.Restrictions.Key))

		dumpFile(b.RestrictionsPath)
		fmt.Fprintln(f, "")
	}
}

func donate() {
	fmt.Println("| DID PINFINDER SAVE THE DAY?")
	fmt.Println("| Please consider donating a few dollars to say thanks!")
	fmt.Println("| https://pinfinder.net/donate")
	fmt.Println("")
}

var syncDir string

func main() {
	allBackups := new(backups)

	fmt.Println("平航 时间限制密码读取工具")
	fmt.Println("使用方法:ph_Restrictions_brup.exe iTunes备份目录 备份密码")

	//fmt.Println("")
	//fmt.Println("PIN Finder", version)
	//fmt.Println("iOS Restrictions Passcode Finder")
	//fmt.Println("https://pinfinder.net")
	fmt.Println()

	flag.Parse()
	if *showLicense {
		displayLicense()
		return
	}
	args := flag.Args()
	switch len(args) {
	case 0:
		os.Exit(1)
		syncDirs, err := findSyncDirs()
		if err != nil {
			exit(101, true, err.Error())
		}

		fmt.Println("iTunes备份目录:", syncDirs)
		fmt.Println("扫描备份文件中...")
		for _, syncDir := range syncDirs {
			if err := allBackups.loadBackups(syncDir, args[1]); err != nil {
				if isBadMacPerms(err); err != nil {
					exitBadMacPerms()
				}
				exit(101, true, err.Error())
			}
		}
	default:
		fmt.Println("iTunes备份目录:", args[0])
		b, err := loadBackup(args[0], args[1])
		if err != nil {
			if isBadMacPerms(err); err != nil {
				exitBadMacPerms()
			}
			exit(101, true, "Invalid backup directory")
		}
		allBackups = &backups{encrypted: b.isEncrypted(), backups: []*backup{b}}

	}

	fmt.Println()

	if *diag {
		var buf bytes.Buffer
		fmt.Println("Generating backup diagnostic report; may take a couple of minutes..")
		generateReport(io.MultiWriter(os.Stdout, &buf), true, allBackups)
		if fn, err := buildDebug("", buf.String(), allBackups); err != nil {
			exit(110, false, err.Error())
		} else {
			fmt.Println("Generated diagnostic report file stored at", fn)
			exit(0, false, "")
		}
	}

	generateReport(os.Stdout, false, allBackups)
	//()
	exit(0, false, "")
}
