package txvalidator

import (
	"bytes"
	"crypto/sha256"
	"fmt"
	"io/ioutil"
	"log"
	"math"
)

type OrgSelector struct {
	hash []byte
	bitString []int
	currentPos int
	orgids []int
	orgidsSet map[int]struct{}
	orgBitLen int
	k int
	n int

	log *	log.Logger
}

func NewOrgSelector(hash []byte, k int, n int) *OrgSelector {
	var os OrgSelector
	
	os.hash = make([]byte, 0, 32)
	os.hash = append(os.hash, hash...)

	os.log = log.New(ioutil.Discard, "orgSelector: ", log.Ltime)
	os.currentPos = 0
	os.k = k
	os.n = n
	os.orgids = make([]int, 0, k)
	os.orgidsSet = make(map[int]struct{})
	os.bitString = calculateBits(hash)
	os.PrintBitString()

	os.orgBitLen = int(math.Ceil(math.Log2(float64(n))))
	os.log.Printf("Org bit length: %d, it is enough for storing id of %d orgs\n", os.orgBitLen, k)

	return &os
}

func (os *OrgSelector) PrintBitString() {
	var output bytes.Buffer
	for _, v := range os.bitString {
		output.WriteString(fmt.Sprint(v))
	}
	os.log.Println(output.String())
}

func (os *OrgSelector) SelectOrgs() []int {
	orgsFound := 0
	for orgsFound < os.k {
		foundId := os.GetOrg()
		if _, ok := os.orgidsSet[foundId]; !ok {
			os.orgidsSet[foundId] = struct{}{}
			os.orgids = append(os.orgids, foundId)
			orgsFound++
		}
	}

	return os.orgids
}

func (os *OrgSelector) GetOrg() int {
	if os.currentPos + os.orgBitLen >= len(os.bitString) {
		os.log.Println("AddBits initiated")
		os.hash = addBits(os.hash)
		os.bitString = calculateBits(os.hash)
	}
	
	bitId := os.bitString[os.currentPos : os.currentPos + os.orgBitLen]
	
	id := 0
	for i := 0; i < os.orgBitLen; i++ {
		id = id + int(math.Pow(2, float64(os.orgBitLen - i - 1))) * bitId[i]
	}
	id = id % os.n

	os.currentPos += os.orgBitLen
	os.log.Printf("Used bits for calculating org: %v -> %d\n", bitId, id)
	return id
}

func (os *OrgSelector) MapToPeerSlice(peers []string) *[]string {
	chosenPeers := make([]string, 0)
	for _, v := range os.orgids {
		chosenPeers = append(chosenPeers, peers[v])
	}

	return &chosenPeers
}

func addBits(src []byte) []byte {
	hash := make([]byte, 0, len(src) + 32)
	hash = append(hash, src...)
	newbits := sha256.Sum256(src)
	for _, v := range newbits {
		hash = append(hash, v)
	}

	return hash
}

func calculateBits(hash []byte) []int {
	bitString := make([]int, 0, len(hash) * 8)

	for _, v := range hash {
		byteBits := getBitsFromByte(v)
		for _, b := range byteBits {
			bitString = append(bitString, b)
		}
	}
	return bitString
}


func getBitsFromByte(b byte) [8]int {
	bi := int(b)
	var bits [8]int
	bits[0] = toBit(bi & 1)
	bits[1] = toBit(bi & 2)
	bits[2] = toBit(bi & 4)
	bits[3] = toBit(bi & 8)
	bits[4] = toBit(bi & 16)
	bits[5] = toBit(bi & 32)
	bits[6] = toBit(bi & 64)
	bits[7] = toBit(bi & 128)

	return bits
}

func toBit(i int) int {
	if i > 0 {
		return 1
	}
	return 0
}