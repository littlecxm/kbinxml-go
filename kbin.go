package kbinxml

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"github.com/beevik/etree"
	"github.com/orcaman/writerseeker"
	"golang.org/x/text/encoding"
	"golang.org/x/text/encoding/charmap"
	"golang.org/x/text/encoding/japanese"
	"golang.org/x/text/transform"
	"io"
	"io/ioutil"
	"math"
	"regexp"
	"strconv"
	"strings"
)

const MagicNumber = 0xa042

type KbinEncoding struct {
	ID      int
	Name    string
	Decoder *encoding.Decoder
	Encoder *encoding.Encoder
}
type KbinNodeType struct {
	Name   string
	Size   int
	Count  int
	Signed bool
}
type ByteOffsets struct {
	offset4 int64
	offset2 int64
	offset1 int64
}

func (b *ByteOffsets) Align(reader io.Seeker) {
	offset, _ := reader.Seek(0, io.SeekCurrent)
	if offset%4 != 0 {
		offset = (offset - offset%4) + 4
	}
	newMaxOffset := int64(math.Max(float64(offset), float64(b.offset4)))
	if offset > b.offset4 {
		b.offset4 = newMaxOffset
	}
	if b.offset2%4 == 0 {
		b.offset2 = newMaxOffset
	}
	if b.offset1%4 == 0 {
		b.offset1 = newMaxOffset
	}
}

var nodeTypes = map[byte]KbinNodeType{
	TypeS8:     {"s8", 1, 1, true},
	TypeU8:     {"u8", 1, 1, false},
	TypeS16:    {"s16", 2, 1, true},
	TypeU16:    {"u16", 2, 1, false},
	TypeS32:    {"s32", 4, 1, true},
	TypeU32:    {"u32", 4, 1, false},
	TypeS64:    {"s64", 8, 1, true},
	TypeU64:    {"u64", 8, 1, false},
	TypeBin:    {"bin", 1, 0, false},
	TypeStr:    {"str", 1, 0, false},
	TypeIp4:    {"ip4", 1, 4, false},
	TypeTime:   {"time", 4, 1, false},
	TypeFloat:  {"float", 4, 1, true},
	TypeDouble: {"double", 8, 1, false},
	Type2s8:    {"2s8", 1, 2, true},
	Type2u8:    {"2u8", 1, 2, false},
	Type2s16:   {"2s16", 2, 2, false},
	Type2u16:   {"2u16", 2, 2, false},
	Type2s32:   {"2s32", 4, 2, true},
	Type2u32:   {"2u32", 4, 2, false},
	Type2s64:   {"2s64", 8, 2, true},
	Type2u64:   {"2u64", 8, 2, false},
	Type2f:     {"2f", 4, 2, false},
	Type2d:     {"2d", 8, 2, false},
	Type3s8:    {"3s8", 1, 3, true},
	Type3u8:    {"3u8", 1, 3, false},
	Type3s16:   {"3s16", 2, 3, false},
	Type3u16:   {"3u16", 2, 3, false},
	Type3s32:   {"3s32", 4, 3, true},
	Type3u32:   {"3u32", 4, 3, false},
	Type3s64:   {"3s64", 8, 3, true},
	Type3u64:   {"3u64", 8, 3, false},
	Type3f:     {"3f", 4, 3, false},
	Type3d:     {"3d", 8, 3, false},
	Type4s8:    {"4s8", 1, 4, true},
	Type4u8:    {"4u8", 1, 4, false},
	Type4s16:   {"4s16", 2, 4, false},
	Type4u16:   {"4u16", 2, 4, false},
	Type4s32:   {"4s32", 4, 4, true},
	Type4u32:   {"4u32", 4, 4, false},
	Type4s64:   {"4s64", 8, 4, true},
	Type4u64:   {"4u64", 8, 4, false},
	Type4f:     {"4f", 4, 4, false},
	Type4d:     {"4d", 8, 4, false},
	TypeVs8:    {"vs8", 1, 16, true},
	TypeVu8:    {"vu8", 1, 16, false},
	TypeVs16:   {"vs16", 2, 8, true},
	TypeVu16:   {"vu16", 2, 8, false},
	TypeBool:   {"bool", 1, 1, false},
	Type2b:     {"2b", 1, 2, false},
	Type3b:     {"3b", 1, 3, false},
	Type4b:     {"4b", 1, 4, false},
	TypeVb:     {"vb", 1, 16, false},
}

var numberTypes = map[string]byte{
	"b":    TypeBool,
	"bool": TypeBool,
	"s8":   TypeS8,
	"u8":   TypeU8,
	"s16":  TypeS16,
	"u16":  TypeU16,
	"s32":  TypeS32,
	"u32":  TypeU32,
	"s64":  TypeS64,
	"u64":  TypeU64,
	"time": TypeTime,
}

const (
	TypeS8     = 2
	TypeU8     = 3
	TypeS16    = 4
	TypeU16    = 5
	TypeS32    = 6
	TypeU32    = 7
	TypeS64    = 8
	TypeU64    = 9
	TypeBin    = 10
	TypeStr    = 11
	TypeIp4    = 12
	TypeTime   = 13
	TypeFloat  = 14
	TypeDouble = 15
	Type2s8    = 16
	Type2u8    = 17
	Type2s16   = 18
	Type2u16   = 19
	Type2s32   = 20
	Type2u32   = 21
	Type2s64   = 22
	Type2u64   = 23
	Type2f     = 24
	Type2d     = 25
	Type3s8    = 26
	Type3u8    = 27
	Type3s16   = 28
	Type3u16   = 29
	Type3s32   = 30
	Type3u32   = 31
	Type3s64   = 32
	Type3u64   = 33
	Type3f     = 34
	Type3d     = 35
	Type4s8    = 36
	Type4u8    = 37
	Type4s16   = 38
	Type4u16   = 39
	Type4s32   = 40
	Type4u32   = 41
	Type4s64   = 42
	Type4u64   = 43
	Type4f     = 44
	Type4d     = 45
	TypeVs8    = 48
	TypeVu8    = 49
	TypeVs16   = 50
	TypeVu16   = 51
	TypeBool   = 52
	Type2b     = 53
	Type3b     = 54
	Type4b     = 55
	TypeVb     = 56
)
const (
	controlNodeStart = 1
	controlAttribute = 46
	controlNodeEnd   = 190
	controlFileEnd   = 191
)

const (
	EncodingNone = iota
	EncodingASCII
	EncodingISO_8859_1
	EncodingEUC_JP
	EncodingSHIFT_JIS
	EncodingUTF_8
)

var encodings = map[byte]*KbinEncoding{
	EncodingNone:       {0, "NONE", nil, nil},
	EncodingASCII:      {1, "ASCII", nil, nil},
	EncodingISO_8859_1: {2, "ISO-8859-1", charmap.ISO8859_1.NewDecoder(), charmap.ISO8859_1.NewEncoder()},
	EncodingEUC_JP:     {3, "EUC-JP", japanese.EUCJP.NewDecoder(), japanese.EUCJP.NewEncoder()},
	EncodingSHIFT_JIS:  {4, "SHIFT_JIS", japanese.ShiftJIS.NewDecoder(), japanese.ShiftJIS.NewEncoder()},
	EncodingUTF_8:      {5, "UTF-8", nil, nil},
}

func DeserializeKbin(input []byte) ([]byte, *KbinEncoding, error) {
	reader := bytes.NewReader(input)

	//Check Magic Number
	magicNumber := make([]byte, 2)
	reader.Read(magicNumber)
	if binary.BigEndian.Uint16(magicNumber) != MagicNumber {
		return nil, nil, errors.New("incorrect magic number")
	}

	//Extract Encoding
	enc, _ := reader.ReadByte()
	documentEncoding := encodings[enc>>5]

	encChk, _ := reader.ReadByte()
	if 0xFF&^enc != encChk {
		return nil, nil, errors.New("invalid encoding checksum, data corruption detected")
	}

	nodes := getSegment(reader)
	data := getSegment(reader)

	document := etree.NewDocument()

	parseDocument(document, nodes, data, documentEncoding)

	parsedXML, err := document.WriteToBytes()
	return parsedXML, documentEncoding, err
}

func parseDocument(document *etree.Document, nodes []byte, data []byte, enc *KbinEncoding) {
	var curNode *etree.Element
	offsets := &ByteOffsets{0, 0, 0}
	nodeReader := bytes.NewReader(nodes)
	dataReader := bytes.NewReader(data)

	for {
		nodeTypeId, _ := nodeReader.ReadByte()

		isArray := false
		if nodeTypeId&0x40 > 0 {
			isArray = true
			nodeTypeId -= 0x40
		}

		nodeType := nodeTypes[nodeTypeId]
		switch nodeTypeId {
		case controlNodeStart:
			name := parseSixbit(nodeReader)
			curNode = newNode(curNode, name)
		case controlAttribute:
			name := parseSixbit(nodeReader)
			dataReader.Seek(offsets.offset4, io.SeekStart)
			attributeValue := getSegment(dataReader)
			offsets.Align(dataReader)
			value := transformString(attributeValue, enc)
			curNode.CreateAttr(name, value)
		case controlNodeEnd:
			if curNode.Parent() != nil {
				curNode = curNode.Parent()
			}
		case controlFileEnd:
			document.AddChild(curNode)
			return
		case TypeStr:
			name := parseSixbit(nodeReader)
			dataReader.Seek(offsets.offset4, io.SeekStart)
			valueBytes := getSegment(dataReader)
			offsets.Align(dataReader)
			value := transformString(valueBytes, enc)
			curNode = addLeaf(curNode, name, value, nodeType.Name, len(value), 0, nodeType)
		case TypeTime, TypeFloat, TypeDouble, TypeU8, TypeS8, TypeU16, TypeS16, TypeU32, TypeS32, TypeU64, TypeS64:
			name := parseSixbit(nodeReader)
			value, dataSize := extractNumber(dataReader, offsets, nodeType, isArray)
			curNode = addLeaf(curNode, name, value, nodeType.Name, int(dataSize), int(dataSize)/nodeType.Size, nodeType)
		case TypeBool, Type2b, Type3b, Type4b:
			name := parseSixbit(nodeReader)
			value, dataSize := extractBool(dataReader, offsets, nodeType, isArray)
			curNode = addLeaf(curNode, name, value, nodeType.Name, int(dataSize), int(dataSize)/nodeType.Size, nodeType)
		case TypeBin:
			name := parseSixbit(nodeReader)
			value, dataSize := extractBin(dataReader, offsets)
			curNode = addLeaf(curNode, name, value, nodeType.Name, int(dataSize), 1, nodeType)
		case TypeIp4:
			name := parseSixbit(nodeReader)
			value := extractIp4(dataReader, offsets)
			curNode = addLeaf(curNode, name, value, nodeType.Name, 0, 0, nodeType)
		default:
			return
		}
	}

}

func extractIp4(reader *bytes.Reader, offsets *ByteOffsets) (output string) {
	reader.Seek(offsets.offset4, io.SeekStart)
	ip := make([]byte, 4)
	reader.Read(ip)
	offsets.Align(reader)

	for _, v := range ip {
		output += fmt.Sprintf("%s.", strconv.Itoa(int(v)))
	}
	output = output[:len(output)-1]
	return
}

func extractBin(reader *bytes.Reader, offsets *ByteOffsets) (output string, dataSize uint32) {
	lengthBytes := make([]byte, 4)
	reader.Seek(offsets.offset4, io.SeekStart)
	reader.Read(lengthBytes)
	offsets.Align(reader)
	dataSize = binary.BigEndian.Uint32(lengthBytes)

	offset := offsets.getOffset(dataSize)

	data := make([]byte, dataSize)
	reader.Seek(*offset, io.SeekStart)
	reader.Read(data)
	offsets.Align(reader)
	return hex.EncodeToString(data), dataSize
}

func addLeaf(curNode *etree.Element, name string, value string, leafType string, size int, count int, nodeType KbinNodeType) *etree.Element {
	curNode = newNode(curNode, name)
	curNode.CreateAttr("__type", leafType)
	if size > nodeType.Size {
		curNode.CreateAttr("__size", strconv.Itoa(size))
	}
	if count > 1 {
		curNode.CreateAttr("__count", strconv.Itoa(count))
	}
	curNode.SetText(value)
	return curNode
}

func extractBool(reader *bytes.Reader, offsets *ByteOffsets, nodeType KbinNodeType, array bool) (output string, dataSize uint32) {
	size := nodeType.Size
	count := nodeType.Count
	if array {
		lengthBytes := make([]byte, 4)
		reader.Seek(offsets.offset4, io.SeekStart)
		reader.Seek(0, io.SeekCurrent)
		reader.Read(lengthBytes)
		offsets.Align(reader)
		dataSize = binary.BigEndian.Uint32(lengthBytes)
		count = int(dataSize) / size
	} else {
		dataSize = uint32(nodeType.Size)
	}
	offset := offsets.getOffset(dataSize)
	reader.Seek(*offset, io.SeekStart)
	for i := 0; i < count; i++ {
		b, _ := reader.ReadByte()
		output += fmt.Sprintf("%b ", b)
	}
	*offset += int64(count * size)
	offsets.Align(reader)
	return output[:len(output)-1], dataSize
}

func (b *ByteOffsets) getOffset(dataSize uint32) *int64 {
	var offset *int64
	switch dataSize {
	case 1:
		offset = &b.offset1
	case 2:
		offset = &b.offset2
	default:
		offset = &b.offset4
	}
	return offset
}

func extractNumber(reader *bytes.Reader, offsets *ByteOffsets, nodeType KbinNodeType, array bool) (output string, dataSize uint32) {
	size := nodeType.Size
	count := nodeType.Count
	if array {
		lengthBytes := make([]byte, 4)
		reader.Seek(offsets.offset4, io.SeekStart)
		reader.Seek(0, io.SeekCurrent)
		reader.Read(lengthBytes)
		offsets.Align(reader)
		dataSize = binary.BigEndian.Uint32(lengthBytes)
		count = int(dataSize) / size
	} else {
		dataSize = uint32(nodeType.Size)
	}
	offset := offsets.getOffset(dataSize)
	reader.Seek(*offset, io.SeekStart)
	for i := 0; i < count; i++ {
		numberBytes := make([]byte, size)
		reader.Read(numberBytes)
		var number uint

		switch size {
		case 1:
			number = uint(numberBytes[0])
		case 2:
			number = uint(binary.BigEndian.Uint16(numberBytes))
		case 4:
			number = uint(binary.BigEndian.Uint32(numberBytes))
		case 8:
			number = uint(binary.BigEndian.Uint64(numberBytes))
		}

		if nodeType.Signed {
			numStr := ""
			switch size {
			case 1:
				numStr = fmt.Sprint(int8(number))
			case 2:
				numStr = fmt.Sprint(int16(number))
			case 4:
				numStr = fmt.Sprint(int32(number))
			case 8:
				numStr = fmt.Sprint(int64(number))
			}
			if nodeType.Name == "float" || nodeType.Name == "double" {
				numStr = numStr[:len(numStr)-6] + "." + numStr[len(numStr)-6:]
			}
			output += fmt.Sprintf("%v ", numStr)
		} else {
			numStr := fmt.Sprint(number)
			if nodeType.Name == "float" || nodeType.Name == "double" {
				numStr = numStr[:len(numStr)-6] + "." + numStr[len(numStr)-6:]
			}
			output += fmt.Sprintf("%v ", numStr)
		}
	}
	*offset += int64(count * size)
	offsets.Align(reader)
	return output[:len(output)-1], dataSize
}
func transformString(input []byte, enc *KbinEncoding) string {
	if input[len(input)-1] == 0 {
		input = input[:len(input)-1]
	}
	if enc.Decoder == nil {
		return string(input)
	}
	transformer := transform.NewReader(bytes.NewReader(input), enc.Decoder)
	newString, _ := ioutil.ReadAll(transformer)
	return string(newString)
}

func newNode(curNode *etree.Element, name string) *etree.Element {
	newNode := etree.NewElement(name)
	if curNode != nil {
		curNode.AddChild(newNode)
	}
	return newNode
}

func parseSixbit(reader *bytes.Reader) string {
	length, _ := reader.ReadByte()
	if length == 0 {
		return ""
	}
	dataLength := int(math.Ceil(float64(length*6) / 8))
	data := make([]byte, dataLength)
	reader.Read(data)

	dataString := ""
	for _, v := range data {
		dataString += fmt.Sprintf("%08b", v)
	}

	output := ""
	for i := 0; i < int(length); i++ {
		chr, _ := strconv.ParseInt(dataString[0:6], 2, 64)
		dataString = dataString[6:]
		if chr < 10 {
			output += string(byte(chr + 48))
		} else if chr == 10 {
			output += ":"
		} else if chr < 37 {
			output += string(byte(chr + 54))
		} else if chr == 37 {
			output += "_"
		} else {
			output += string(byte(chr + 59))
		}
	}
	return output
}

func getSegment(reader *bytes.Reader) []byte {
	length := make([]byte, 4)
	reader.Read(length)
	segment := make([]byte, binary.BigEndian.Uint32(length))
	reader.Read(segment)
	return segment
}

func SerializeKbin(document *etree.Document, encoding int) (output []byte) {
	output = append(output, []byte{0xa0, 0x42}...)

	// Add encoding and checksum
	output = append(output, []byte{byte(encoding << 5), byte(0xFF &^ (encoding << 5))}...)
	iw := IterWalk(document)

	nodes := make([]byte, 0)
	data := make([]byte, 0)
	encoder := encodings[byte(encoding)]

	dataWriter := &writerseeker.WriterSeeker{}

	offsets := &ByteOffsets{}

	node, event := document.Root(), "start"
	for {
		if event == "end" {
			nodes = append(nodes, controlNodeEnd|0x40)
			node, event = iw.Walk()
			continue
		} else if event == "eof" {
			nodes = append(nodes, controlFileEnd|0x40)
			if len(nodes)%4 != 0 {
				nodes = append(nodes, bytes.Repeat([]byte{00}, 4-(len(nodes)%4))...)
			}
			data, _ = ioutil.ReadAll(dataWriter.Reader())
			data = append(data, bytes.Repeat([]byte{00}, int(offsets.offset4)-len(data))...)
			break
		}

		leafAttr := node.SelectAttr("__type")
		if leafAttr != nil { // leaf
			switch node.SelectAttr("__type").Value {
			case "str":
				nodes = append(nodes, []byte{TypeStr, byte(len(node.Tag))}...)
				nodes = append(nodes, toSixbit(node.Tag)...)
				attrLength := make([]byte, 4)
				value, _ := encoder.Encoder.Bytes([]byte(node.Text()))
				value = append(value, 0x00)

				binary.BigEndian.PutUint32(attrLength, uint32(len(value)))
				dataWriter.Seek(offsets.offset4, io.SeekStart)
				dataWriter.Write(attrLength)
				offsets.Align(dataWriter)

				dataWriter.Seek(offsets.offset4, io.SeekStart)
				dataWriter.Write(value)
				offsets.Align(dataWriter)
			case "bin":
				nodes = append(nodes, []byte{TypeBin, byte(len(node.Tag))}...)
				nodes = append(nodes, toSixbit(node.Tag)...)
				binLength := make([]byte, 4)
				data, _ := hex.DecodeString(node.Text())

				binary.BigEndian.PutUint32(binLength, uint32(len(data)))
				dataWriter.Seek(offsets.offset4, io.SeekStart)
				dataWriter.Write(binLength)
				offsets.Align(dataWriter)

				dataWriter.Seek(offsets.offset4, io.SeekStart)
				dataWriter.Write(data)
				offsets.Align(dataWriter)
			case "f", "float":
				nodes = append(nodes, []byte{TypeFloat, byte(len(node.Tag))}...)
				nodes = append(nodes, toSixbit(node.Tag)...)
				dataWriter.Seek(offsets.offset4, io.SeekStart)
				floatStr := node.Text()
				floatLst := strings.Split(floatStr, ".")
				floatMajor := floatLst[0]
				floatMinor := floatLst[1]
				if len(floatMinor) > 6 {
					floatMinor = floatMinor[0:6]
				} else if len(floatMinor) < 6 {
					floatMinor += strings.Repeat("0", 6-len(floatMinor))
				}
				floatInt, _ := strconv.Atoi(floatMajor + floatMinor)
				floatBytes := make([]byte, 4)
				binary.BigEndian.PutUint32(floatBytes, uint32(floatInt))
				dataWriter.Write(floatBytes)
				offsets.Align(dataWriter)
			case "ip4":
				num := TypeIp4
				addresses := strings.Split(node.Text(), " ")
				realNum := byte(num)
				if len(addresses) > 1 {
					realNum |= 0x40
				}
				if len(addresses) > 1 {
					arrayLength := make([]byte, 4)
					binary.BigEndian.PutUint32(arrayLength, uint32(len(addresses)*4))
					dataWriter.Seek(offsets.offset4, io.SeekStart)
					dataWriter.Write(arrayLength)
					offsets.Align(dataWriter)
				}
				dataWriter.Seek(offsets.offset4, io.SeekStart)
				nodes = append(nodes, []byte{realNum, byte(len(node.Tag))}...)
				nodes = append(nodes, toSixbit(node.Tag)...)
				for _, addr := range addresses {
					addrLst := strings.Split(addr, ".")
					for _, a := range addrLst {
						aa, _ := strconv.ParseUint(a, 10, 8)
						dataWriter.Write([]byte{byte(aa)})
					}
				}
				offsets.Align(dataWriter)

			case "time", "b", "bool", "u8", "s8", "u16", "s16", "u32", "s32", "u64", "s64":
				num := numberTypes[node.SelectAttr("__type").Value]
				numbers := strings.Split(node.Text(), " ")
				realNum := num
				if len(numbers) > 1 {
					realNum |= 0x40
				}
				nodes = append(nodes, []byte{realNum, byte(len(node.Tag))}...)
				nodes = append(nodes, toSixbit(node.Tag)...)
				nt := nodeTypes[num]
				size := nt.Size * len(numbers)

				if len(numbers) > 1 {
					arrayLength := make([]byte, 4)
					binary.BigEndian.PutUint32(arrayLength, uint32(size))
					dataWriter.Seek(offsets.offset4, io.SeekStart)
					dataWriter.Write(arrayLength)
					offsets.Align(dataWriter)
				}
				offset := &offsets.offset1
				if size == 2 {
					offset = &offsets.offset2
				} else if size > 2 {
					offset = &offsets.offset4
				}

				dataWriter.Seek(*offset, io.SeekStart)
				for _, v := range numbers {
					var numberBytes = make([]byte, nt.Size)

					switch nt.Size {
					case 1:
						number, _ := strconv.Atoi(v)
						numberBytes[0] = byte(number)
					case 2:
						var number uint16
						if nt.Signed {
							num, _ := strconv.ParseInt(v, 10, 16)
							number = uint16(num)
						} else {
							num, _ := strconv.ParseUint(v, 10, 16)
							number = uint16(num)
						}
						binary.BigEndian.PutUint16(numberBytes, number)
					case 4:
						var number uint32
						if nt.Signed {
							num, _ := strconv.ParseInt(v, 10, 32)
							number = uint32(num)
						} else {
							num, _ := strconv.ParseUint(v, 10, 32)
							number = uint32(num)
						}
						binary.BigEndian.PutUint32(numberBytes, number)
					case 8:
						var number uint64
						if nt.Signed {
							num, _ := strconv.ParseInt(v, 10, 64)
							number = uint64(num)
						} else {
							number, _ = strconv.ParseUint(v, 10, 64)
						}

						binary.BigEndian.PutUint64(numberBytes, number)
					}
					dataWriter.Write(numberBytes)
					if node.Tag == "s_coin" {
					}
				}
				*offset += int64(size)
				offsets.Align(dataWriter)
			default:
				panic(fmt.Sprintf("Unsupported type %v", node.SelectAttr("__type").Value))
			}
			for _, v := range node.Attr {
				if v.Key != "__type" && v.Key != "__count" && v.Key != "__size" {
					nodes = append(nodes, controlAttribute)
					nodes = append(nodes, byte(len(v.Key)))
					nodes = append(nodes, toSixbit(v.Key)...)

					attrLength := make([]byte, 4)
					value, _ := encoder.Encoder.Bytes([]byte(v.Value))
					value = append(value, 0x00)

					binary.BigEndian.PutUint32(attrLength, uint32(len(value)))
					dataWriter.Seek(offsets.offset4, io.SeekStart)
					dataWriter.Write(attrLength)
					offsets.Align(dataWriter)

					dataWriter.Seek(offsets.offset4, io.SeekStart)
					dataWriter.Write(value)
					offsets.Align(dataWriter)
				}
			}

		} else { // node
			nodes = append(nodes, []byte{controlNodeStart, byte(len(node.Tag))}...)
			nodes = append(nodes, toSixbit(node.Tag)...)
			for _, v := range node.Attr {
				nodes = append(nodes, controlAttribute)
				nodes = append(nodes, byte(len(v.Key)))
				nodes = append(nodes, toSixbit(v.Key)...)

				attrLength := make([]byte, 4)
				value, _ := encoder.Encoder.Bytes([]byte(v.Value))
				value = append(value, 0x00)

				binary.BigEndian.PutUint32(attrLength, uint32(len(value)))
				dataWriter.Seek(offsets.offset4, io.SeekStart)
				dataWriter.Write(attrLength)
				offsets.Align(dataWriter)

				dataWriter.Seek(offsets.offset4, io.SeekStart)
				dataWriter.Write(value)
				offsets.Align(dataWriter)
			}
		}

		node, event = iw.Walk()
	}
	nodeLength := make([]byte, 4)
	dataLength := make([]byte, 4)
	binary.BigEndian.PutUint32(nodeLength, uint32(len(nodes)))
	binary.BigEndian.PutUint32(dataLength, uint32(len(data)))
	output = append(output, nodeLength...)
	output = append(output, nodes...)
	output = append(output, dataLength...)
	output = append(output, data...)
	return
}

func toSixbit(text string) (output []byte) {
	bitstring := ""
	for _, v := range text {
		var char int32
		if match, _ := regexp.Match("[0-9]", []byte{byte(v)}); match {
			char = v - 48
		} else if match, _ := regexp.Match(":", []byte{byte(v)}); match {
			char = 10
		} else if match, _ := regexp.Match("[A-Z]", []byte{byte(v)}); match {
			char = v - 54
		} else if match, _ := regexp.Match("_", []byte{byte(v)}); match {
			char = 37
		} else if match, _ := regexp.Match("[a-z]", []byte{byte(v)}); match {
			char = v - 59
		} else {
			panic(fmt.Sprintf("invalid sixbit char %v", v))
		}
		bitstring += fmt.Sprintf("%08b", char)[2:]
	}
	if len(bitstring)%8 != 0 {
		extra := 8 - (len(bitstring) % 8)
		bitstring += strings.Repeat("0", extra)
	}
	for i := 0; i < len(bitstring); i += 8 {
		outbyte, _ := strconv.ParseUint(bitstring[i:i+8], 2, 64)
		output = append(output, byte(outbyte))
	}
	return
}
