/* -*- mode: C++; c-basic-offset: 4; tab-width: 4 -*-
 *
 * Copyright (c) 2011 Apple Inc. All rights reserved.
 *
 * @APPLE_LICENSE_HEADER_START@
 *
 * This file contains Original Code and/or Modifications of Original Code
 * as defined in and that are subject to the Apple Public Source License
 * Version 2.0 (the 'License'). You may not use this file except in
 * compliance with the License. Please obtain a copy of the License at
 * http://www.opensource.apple.com/apsl/ and read it before using this
 * file.
 *
 * The Original Code and all software distributed under the License are
 * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
 * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,
 * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.
 * Please see the License for the specific language governing rights and
 * limitations under the License.
 *
 * @APPLE_LICENSE_HEADER_END@
 */

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/stat.h>
#include <string.h>
#include <fcntl.h>
#include <stdlib.h>
#include <errno.h>
#include <sys/mman.h>
#include <sys/syslimits.h>
#include <libkern/OSByteOrder.h>
#include <mach-o/arch.h>
#include <mach-o/loader.h>
#include <Availability.h>

#include "CodeSigningTypes.h"
#include <CommonCrypto/CommonHMAC.h>
#include <CommonCrypto/CommonDigest.h>
// #include <CommonCrypto/CommonDigestSPI.h>

#define NO_ULEB
#include "Architectures.hpp"
#include "MachOFileAbstraction.hpp"
#include "CacheFileAbstraction.hpp"

#include "dsc_iterator.h"
#include "dsc_extractor.h"
#include "MachOTrie.hpp"
#include "SupportedArchs.h"
#include "DyldSharedCache.h"

#include <vector>
#include <set>
#include <map>
#include <unordered_map>
#include <algorithm>
#include <dispatch/dispatch.h>
#include <string>
#include <mach/mach.h>


struct seg_info
{
    seg_info(const char* n, uint64_t o, uint64_t s)
    : segName(n), offset(o), sizem(s) { }
    const char* segName;
    uint64_t    offset;
    uint64_t    sizem;
};

typedef struct {
    uint64_t cache_offset;
    uint64_t cache_segsize;
    uint64_t dylib_offset;
} offset_correlator;

typedef struct {
    uint64_t sect_vmaddr;
    uint64_t sect_size;
    uint64_t sect_dylib_offset;
} section_offset_correlator;
class CStringHash {
public:
    size_t operator()(const char* __s) const {
        size_t __h = 0;
        for ( ; *__s; ++__s)
            __h = 5 * __h + *__s;
        return __h;
    };
};
class CStringEquals {
public:
    bool operator()(const char* left, const char* right) const { return (strcmp(left, right) == 0); }
};
typedef std::unordered_map<const char*, std::vector<seg_info>, CStringHash, CStringEquals> NameToSegments;

// Filter to find individual symbol re-exports in trie
class NotReExportSymbol {
public:
    NotReExportSymbol(const std::set<int> &rd) :_reexportDeps(rd) {}
    bool operator()(const mach_o::trie::Entry &entry) const {
        bool result = isSymbolReExport(entry);
        if (result) {
            // <rdar://problem/17671438> Xcode 6 leaks in dyld_shared_cache_extract_dylibs
            ::free((void*)entry.name);
            const_cast<mach_o::trie::Entry*>(&entry)->name = NULL;
        }
        return result;
    }
private:
    bool isSymbolReExport(const mach_o::trie::Entry &entry) const {
        if ( (entry.flags & EXPORT_SYMBOL_FLAGS_KIND_MASK) != EXPORT_SYMBOL_FLAGS_KIND_REGULAR )
            return true;
        if ( (entry.flags & EXPORT_SYMBOL_FLAGS_REEXPORT) == 0 )
            return true;
        // If the symbol comes from a dylib that is re-exported, this is not an individual symbol re-export
        if ( _reexportDeps.count((int)entry.other) != 0 )
            return true;
        return false;
    }
    const std::set<int> &_reexportDeps;
};

static void append_uleb128(uint64_t value, std::vector<uint8_t>& out)
{
    uint8_t byte;
    do {
        byte = value & 0x7F;
        value &= ~0x7F;
        if (value != 0)
            byte |= 0x80;
        out.push_back(byte);
        value = value >> 7;
    } while (byte >= 0x80);
}

class RebaseMaker {
public:
    std::vector<uint8_t> relocs;
    uintptr_t            segmentStartMapped;
    uintptr_t            segmentEndMapped;
    int32_t              currentSegment;
    RebaseMaker(int32_t _currentSegment, uintptr_t _segmentStartMapped, uintptr_t _segmentEndMapped)
        : currentSegment(_currentSegment)
        , segmentStartMapped(_segmentStartMapped)
        , segmentEndMapped(_segmentEndMapped)
    {
        relocs.push_back(REBASE_OPCODE_SET_TYPE_IMM | REBASE_TYPE_POINTER);
    }
    void addSlide(uint8_t* loc)
    {
        uintptr_t l = (uintptr_t)loc;
        if (l < segmentStartMapped || l >= segmentEndMapped) {
            abort();
            return;
        }
        addReloc(currentSegment, l - segmentStartMapped);
    }
    void addReloc(int32_t segment, uintptr_t segmentOffset)
    {
        relocs.push_back(REBASE_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB | segment);
        append_uleb128(segmentOffset, relocs);
        relocs.push_back(REBASE_OPCODE_DO_REBASE_IMM_TIMES | 1);
    }
    void finish()
    {
        relocs.push_back(REBASE_OPCODE_DONE);
    }
};

static void rebaseChain(uint8_t* pageContent, uint16_t startOffset, uintptr_t slideAmount, const dyldCacheSlideInfo2<LittleEndian>* slideInfo, uint8_t* filePage, uint8_t* segmentStart, uint8_t* segmentEnd, RebaseMaker& slides, std::vector<section_offset_correlator>& section_adjustments)
{
    uintptr_t deltaMask = 0xffffffffffffffff;
    uintptr_t valueAdd = 0;
    if (slideInfo != NULL)
    {
        deltaMask = (uintptr_t)(slideInfo->delta_mask());
        valueAdd = (uintptr_t)(slideInfo->value_add());
    }
    const uintptr_t valueMask = ~deltaMask;
    const unsigned  deltaShift = __builtin_ctzll(deltaMask) - 2;
    uint32_t pageOffset = startOffset;
    uint32_t delta = 1;
    while (delta != 0) {
        uint8_t*  loc = pageContent + pageOffset;

        uintptr_t rawValue = *((uintptr_t*)loc);

        delta = (uint32_t)((rawValue & deltaMask) >> deltaShift);
        // printf("delta: %d\n", delta);

        uintptr_t value = (rawValue & valueMask);

        if(value !=0)
        {
         
            //adjust value to the rebased VMaddr before 
            //looking up that vmaddr to find the dylib offset adjustment
            value += valueAdd;
            value += slideAmount;
            for(const section_offset_correlator& soc: section_adjustments)
            {
                uint64_t sect_start = soc.sect_vmaddr;
                uint64_t sect_end = sect_start + soc.sect_size;
                if(value >= sect_start && value < sect_end)
                {
                    uint64_t fixup = soc.sect_vmaddr - soc.sect_dylib_offset;
                    value = value - fixup;
                }
            }
        }

        //*((uintptr_t*)loc) = value;
        if (rawValue == 0x20045413F3B || rawValue == 0x00007fff653d9bee) {
            printf("rawValue: %p\n", (void *)rawValue);
            printf("adjusted value: %p\n", (void *)value);
        }
        printf("values: %p,%p\n", (void*)rawValue, (void*)value);
        uint8_t* outLoc = filePage + pageOffset;
        // printf("outLoc: %p\n", outLoc);
        // printf("*outloc: %p\n", *((uintptr_t*)outLoc));
        if (outLoc >= segmentStart && outLoc < segmentEnd)
        {
            if (*((uintptr_t*)outLoc) != rawValue) {
                abort();
            }
            *((uintptr_t*)outLoc) = value;
            slides.addSlide(outLoc);
        }
        //dyld::log("         pageOffset=0x%03X, loc=%p, org value=0x%08llX, new value=0x%08llX, delta=0x%X\n", pageOffset, loc, (uint64_t)rawValue, (uint64_t)value, delta);
        pageOffset += delta;
    }
}

template <typename A>
std::vector<uint8_t> slideOutput(macho_header<typename A::P>* mh, uint64_t textOffsetInCache, const void* mapped_cache, std::vector<section_offset_correlator>& section_adjustments, std::vector<uint64_t>& saved_vmaddrs)
{
    typedef typename A::P P;

    // auto dataSegment = mh->getSegment("__DATA");

    // grab the slide information from the cache
    const dyldCacheHeader<LittleEndian>*      header = (dyldCacheHeader<LittleEndian>*)mapped_cache;
    const dyldCacheFileMapping<LittleEndian>* mappings = (dyldCacheFileMapping<LittleEndian>*)((char*)mapped_cache + header->mappingOffset());
    for(int i=0; i < header->mappingCount(); i++){
        const dyldCacheFileMapping<LittleEndian>* m = &mappings[i];
        // m->set_address(m->file_offset)
        printf("mapping[%d]: address: %p, size:[0x%llx], file_offset: %p\n", i, (void*)m->address(), m->size(), (void *)m->file_offset());
        printf("saved vmaddr[%d]: %p\n", i, (void *)saved_vmaddrs[i]);
    }
    const dyldCacheFileMapping<LittleEndian>* dataMapping = &mappings[1];
    uint64_t                                  dataStartAddress = dataMapping->address();
    printf("data start address: %p\n", (void*)dataStartAddress);
    const dyldCacheSlideInfo<LittleEndian>*   slideInfo = NULL;
    const dyldCacheSlideInfo2<LittleEndian>*  slideHeader = NULL;
    uint32_t                            page_size = 0;
    const uint16_t*                           page_starts = NULL;
    const uint16_t*                           page_extras = NULL;


    if (header->slideInfoSize() > 0)
    {
        slideInfo = (dyldCacheSlideInfo<LittleEndian>*)((char*)mapped_cache + header->slideInfoOffset());
        slideHeader = (dyldCacheSlideInfo2<LittleEndian>*)(slideInfo);
    }else
    {
        printf("Getting slide infos from slide descriptor table\n");
        
        uint32_t slide_info_descriptor_offset = header->mappingWithSlideOffset();
        printf("slide info descriptor offset: 0x%x\n", slide_info_descriptor_offset);

        dyld_cache_slide_descriptor* descriptors
            = (dyld_cache_slide_descriptor*)((char*)mapped_cache + slide_info_descriptor_offset);
        for(int i=0; i < header->mappingWithSlideCount(); i++){
            dyld_cache_slide_descriptor* slide_descriptor = &descriptors[i];
            if (slide_descriptor->slide_info_size > 0)
            {
                printf("slide info descriptor idx: %d\n", i);
                uint64_t slide_info_offset = slide_descriptor->slide_info_off;
                printf("Slide info offset: 0x%016llx\n", slide_info_offset);
                slideInfo = (dyldCacheSlideInfo<LittleEndian>*)((char*)mapped_cache + slide_info_offset);
                slideHeader = (dyldCacheSlideInfo2<LittleEndian>*)(slideInfo);
                break;
            }
        }
    }

    if(NULL != slideInfo){
        page_size = slideHeader->page_size();
        page_starts = (uint16_t*)((long)(slideInfo) + slideHeader->page_starts_offset());
        page_extras = (uint16_t*)((long)(slideInfo) + slideHeader->page_extras_offset());
    }

    auto slide = 0;
    auto slideOneSegment = [=](const macho_segment_command<P>* segment, int segmentIndex, uint64_t vmaddr, std::vector<section_offset_correlator>& section_adjustments) {
        auto        segmentInFile = (uint8_t*)mh + segment->fileoff();
        RebaseMaker rebaseMaker(segmentIndex, (uintptr_t)segmentInFile, (uintptr_t)(segmentInFile + segment->filesize()));

        uint64_t _vmaddr = vmaddr;
        // uint64_t _vmaddr = segment->vmaddr();
        printf("_vmaddr: %p\n", (void *)_vmaddr);
        uint64_t startAddr = _vmaddr - dataStartAddress;

        printf("startAddr: %p\n", (void *)startAddr);
        uint64_t    startPage = startAddr / 0x1000;
        uint32_t    startAddrOff = startAddr & 0xfff;
        printf("startAddrOff: 0x%x\n", startAddrOff);
        uint64_t    endPage = (((_vmaddr + segment->vmsize() + 0xfffull) & ~0xfffull) - dataStartAddress) / 0x1000;
        auto        segmentEnd = segmentInFile + segment->filesize();
        for (uint64_t i = startPage; i < endPage; ++i) {
            uint8_t* filePage = segmentInFile + ((i - startPage) * 0x1000) - startAddrOff;
            uint8_t* page = (uint8_t*)mapped_cache + dataMapping->file_offset() + (i * 0x1000);
            uint16_t pageEntry = 0;
            if (page_starts != NULL){
                pageEntry = page_starts[i];
            }
            printf("page_starts[%llu]=0x%04X\n", i, pageEntry);
            if (pageEntry == DYLD_CACHE_SLIDE_PAGE_ATTR_NO_REBASE)
            {
                printf("DYLD_CACHE_SLIDE_PAGE_ATTR_NO_REBASE\n");
                continue;
            }
            if (pageEntry & DYLD_CACHE_SLIDE_PAGE_ATTR_EXTRA) {
                uint16_t chainIndex = (pageEntry & 0x3FFF);
                bool     done = false;
                while (!done) {
                    uint16_t info = page_extras[chainIndex];
                    uint16_t pageStartOffset = (info & 0x3FFF) * 4;
                    printf("     chain[%d] pageOffset=0x%03X\n", chainIndex, pageStartOffset);
                    rebaseChain(page, pageStartOffset, slide, slideHeader, filePage, segmentInFile, segmentEnd, rebaseMaker, section_adjustments);
                    done = (info & DYLD_CACHE_SLIDE_PAGE_ATTR_END);
                    ++chainIndex;
                }
            } else {
                uint32_t pageOffset = pageEntry * 4;
                printf("     start pageOffset=0x%03X\n", pageOffset);
                rebaseChain(page, pageOffset, slide, slideHeader, filePage, segmentInFile, segmentEnd, rebaseMaker, section_adjustments);
            }
        }
        rebaseMaker.finish();
        return rebaseMaker.relocs;
    };
    printf("sliding __DATA\n");
    auto ret = slideOneSegment(mh->getSegment("__DATA"), 1, saved_vmaddrs[1], section_adjustments);
    auto constData = mh->getSegment("__DATA_CONST");
    if (constData) {
        printf("sliding __DATA_CONST\n");
        auto c = slideOneSegment(constData, 2, saved_vmaddrs[2], section_adjustments);
        ret.insert(ret.end() - 1, c.begin(), c.end());
    }
    return ret;
}

template <typename P>
struct LoadCommandInfo {
};

template <typename A>
class LinkeditOptimizer {
    typedef typename A::P P;
    typedef typename A::P::E E;
    typedef typename A::P::uint_t pint_t;

private:
    macho_segment_command<P>* linkEditSegCmd = NULL;
    macho_symtab_command<P>* symtab = NULL;
    macho_dysymtab_command<P>*    dynamicSymTab = NULL;
    macho_linkedit_data_command<P>*    functionStarts = NULL;
    macho_linkedit_data_command<P>*    dataInCode = NULL;
    uint32_t exportsTrieOffset = 0;
    uint32_t exportsTrieSize = 0;
    std::set<int> reexportDeps;
    std::vector<section_offset_correlator> section_adjustments;


public:
    void optimize_loadcommands(macho_header<typename A::P>* mh, uint64_t textOffsetInCache, const void* mapped_cache, const std::vector<seg_info>& segments)
    {
        typedef typename A::P P;
        typedef typename A::P::E E;
        typedef typename A::P::uint_t pint_t;

        // update header flags
        mh->set_flags(mh->flags() & 0x7FFFFFFF); // remove in-cache bit

        // update load commands
        const dyldCacheHeader<LittleEndian>*      header = (dyldCacheHeader<LittleEndian>*)mapped_cache;
        uint64_t cumulativeFileSize = 0;
        const unsigned origLoadCommandsSize = mh->sizeofcmds();
        unsigned bytesRemaining = origLoadCommandsSize;
        unsigned removedCount = 0;
        const macho_load_command<P>* const cmds = (macho_load_command<P>*)((uint8_t*)mh + sizeof(macho_header<P>));
        const uint32_t cmdCount = mh->ncmds();
        std::vector<uint64_t> saved_vmaddrs;
        saved_vmaddrs.reserve(cmdCount);
        std::vector<offset_correlator> offsets_map;
        offsets_map.reserve(header->mappingCount());
        section_adjustments.reserve(255); //max sections
        const macho_load_command<P>* cmd = cmds;
        int depIndex = 0;
        uint32_t sect_count = 0;
        macho_dyld_info_command<P>* dyldInfo = NULL;
        for (uint32_t i = 0; i < cmdCount; ++i) {
            bool remove = false;

            switch ( cmd->cmd() ) {
                case macho_segment_command<P>::CMD:
                {
                    // update segment/section file offsets
                    macho_segment_command<P>* segCmd = (macho_segment_command<P>*)cmd;
                    segCmd->set_fileoff(cumulativeFileSize);
                    segCmd->set_filesize(segCmd->vmsize());
                    macho_section<P>* const sectionsStart = (macho_section<P>*)((char*)segCmd + sizeof(macho_segment_command<P>));
                    macho_section<P>* const sectionsEnd = &sectionsStart[segCmd->nsects()];
                    for(macho_section<P>* sect = sectionsStart; sect < sectionsEnd; ++sect) {
                        uint64_t fileoff = 0;
                        uint64_t off_into_segment = sect->addr() - segCmd->vmaddr();
                        fileoff = (cumulativeFileSize + off_into_segment);
                        // section_adjustments[sect_count] = sect->addr() - fileoff;
                        section_offset_correlator soc = {sect->addr(), sect->size(), fileoff};
                        section_adjustments.push_back(soc);

                        sect_count++;
                        sect->set_addr(fileoff);
                        if ( sect->offset() != 0 )
                        {
                            sect->set_offset((uint32_t)fileoff);
                        }
                        printf("sect->offset(): 0x%08x\n", sect->offset());
                        printf("sect->addr(): %p\n", (void *)sect->addr());
                    }
                    saved_vmaddrs[i] = segCmd->vmaddr();
                    segCmd->set_vmaddr((cumulativeFileSize + 0xfff) & ~0xfff);
                    offset_correlator correlator;

                    if(i < segments.size())
                    {
                        const seg_info& cache_seg = segments[i];
                        correlator.cache_offset = cache_seg.offset;
                        correlator.cache_segsize = cache_seg.sizem;
                        correlator.dylib_offset = segCmd->fileoff();
                        offsets_map.push_back(correlator);
                    }

                    printf("seg vmaddr: %p\n", (void*)segCmd->vmaddr());
                    if ( strcmp(segCmd->segname(), "__LINKEDIT") == 0 ) {
                        printf("Got linkEditSegCmd\n");
                        linkEditSegCmd = segCmd;
                    }
                    cumulativeFileSize += segCmd->filesize();
                    break;
                }
                case LC_DYLD_INFO_ONLY:
                {
                    // zero out all dyld info
                    printf("Got dyldInfo\n");
                    dyldInfo = (macho_dyld_info_command<P>*)cmd;
                    exportsTrieOffset = dyldInfo->export_off();
                    exportsTrieSize = dyldInfo->export_size();
                    dyldInfo->set_rebase_off(0);
                    dyldInfo->set_rebase_size(0);
                    dyldInfo->set_bind_off(0);
                    dyldInfo->set_bind_size(0);
                    dyldInfo->set_weak_bind_off(0);
                    dyldInfo->set_weak_bind_size(0);
                    dyldInfo->set_lazy_bind_off(0);
                    dyldInfo->set_lazy_bind_size(0);
                    dyldInfo->set_export_off(0);
                    dyldInfo->set_export_size(0);
                }
                    break;
                case LC_SYMTAB:
                    symtab = (macho_symtab_command<P>*)cmd;
                    break;
                case LC_DYSYMTAB:
                    dynamicSymTab = (macho_dysymtab_command<P>*)cmd;
                    break;
                case LC_FUNCTION_STARTS:
                    functionStarts = (macho_linkedit_data_command<P>*)cmd;
                    break;
                case LC_DATA_IN_CODE:
                    dataInCode = (macho_linkedit_data_command<P>*)cmd;
                    break;
                case LC_LOAD_DYLIB:
                case LC_LOAD_WEAK_DYLIB:
                case LC_REEXPORT_DYLIB:
                case LC_LOAD_UPWARD_DYLIB:
                    ++depIndex;
                    if ( cmd->cmd() == LC_REEXPORT_DYLIB ) {
                        reexportDeps.insert(depIndex);
                    }
                    break;
                case LC_SEGMENT_SPLIT_INFO:
                    // <rdar://problem/23212513> dylibs iOS 9 dyld caches have bogus LC_SEGMENT_SPLIT_INFO
                    remove = true;
                    break;
            }
            uint32_t cmdSize = cmd->cmdsize();
            macho_load_command<P>* nextCmd = (macho_load_command<P>*)(((uint8_t*)cmd)+cmdSize);
            if ( remove ) {
                ::memmove((void*)cmd, (void*)nextCmd, bytesRemaining);
                ++removedCount;
            }
            else {
                bytesRemaining -= cmdSize;
                cmd = nextCmd;
            }
        }
        // zero out stuff removed
        ::bzero((void*)cmd, bytesRemaining);
        // update header
        mh->set_ncmds(cmdCount - removedCount);
        mh->set_sizeofcmds(origLoadCommandsSize - bytesRemaining);

        if(dyldInfo != NULL && linkEditSegCmd != NULL)
        {
            // remove the slide linked list from the dyld cache
            // and generate crappy rebase info
            std::vector<uint8_t> rebaseInfo = slideOutput<A>(mh, textOffsetInCache, mapped_cache, section_adjustments, saved_vmaddrs);

            // linkEditSegCmd->set_fileoff((linkEditSegCmd->fileoff() + 0xfff) & ~0xfff);

            // const uint64_t newDyldInfoOffset = linkEditSegCmd->fileoff();
            // uint64_t       newDyldInfoSize = 0;

            //Disabling all this below because it breaks a bunch of things that follow
            //Not sure if there's a way to recalculate everything elase after we insert this

            //memcpy((char*)mh + newDyldInfoOffset + newDyldInfoSize, (char*)mapped_cache + dyldInfo->rebase_off(), dyldInfo->rebase_size());
            // memcpy((char*)mh + newDyldInfoOffset + newDyldInfoSize, rebaseInfo.data(), rebaseInfo.size());
            // dyldInfo->set_rebase_size((rebaseInfo.size() + 0x7u) & ~0x7u);
            // dyldInfo->set_rebase_off(newDyldInfoOffset + newDyldInfoSize);
            // newDyldInfoSize += dyldInfo->rebase_size();

            // memcpy((char*)mh + newDyldInfoOffset + newDyldInfoSize, (char*)mapped_cache + dyldInfo->bind_off(), dyldInfo->bind_size());
            // dyldInfo->set_bind_off(newDyldInfoOffset + newDyldInfoSize);
            // newDyldInfoSize += dyldInfo->bind_size();

            // memcpy((char*)mh + newDyldInfoOffset + newDyldInfoSize, (char*)mapped_cache + dyldInfo->lazy_bind_off(), dyldInfo->lazy_bind_size());
            // dyldInfo->set_lazy_bind_off(newDyldInfoOffset + newDyldInfoSize);
            // newDyldInfoSize += dyldInfo->lazy_bind_size();

            // memcpy((char*)mh + newDyldInfoOffset + newDyldInfoSize, (char*)mapped_cache + dyldInfo->export_off(), dyldInfo->export_size());
            // dyldInfo->set_export_off(newDyldInfoOffset + newDyldInfoSize);
        }
    }

    void fixup_symtab(std::vector<macho_nlist<P>>& newSymTab, const void* mapped_cache)
    {
        uint64_t count = 0;
        printf("Fixing up symbols\n");
        for (macho_nlist<P>& s : newSymTab)
        {
            if((s.n_type() & N_STAB) == 0){

                if(s.n_type() & N_SECT)
                {
                    count++;
                    section_offset_correlator soc = section_adjustments[s.n_sect()];
                    uint64_t fixup = soc.sect_vmaddr - soc.sect_dylib_offset;
                    uint64_t newaddr = s.n_value() - fixup;
                    s.set_n_value(newaddr);
                }
            }
        }
        printf("Fixed %llu symbols\n", count);
    }

    int optimize_linkedit(std::vector<uint8_t>& new_linkedit_data, uint64_t textOffsetInCache, const void* mapped_cache)
    {
        typedef typename A::P P;
        typedef typename A::P::E E;
        typedef typename A::P::uint_t pint_t;

        // rebuild symbol table
        if ( linkEditSegCmd == NULL ) {
            fprintf(stderr, "__LINKEDIT not found\n");
            return -1;
        }
        if ( symtab == NULL ) {
            fprintf(stderr, "LC_SYMTAB not found\n");
            return -1;
        }
        if ( dynamicSymTab == NULL ) {
            fprintf(stderr, "LC_DYSYMTAB not found\n");
            return -1;
        }

        const uint64_t newFunctionStartsOffset = new_linkedit_data.size();
        uint32_t functionStartsSize = 0;
        if ( functionStarts != NULL ) {
            // copy function starts from original cache file to new mapped dylib file
            functionStartsSize = functionStarts->datasize();
            printf("functionStarts->dataoff(): 0x%08x\n", functionStarts->dataoff());
            printf("functionStartsSize: 0x%x\n", functionStartsSize);
            new_linkedit_data.insert(new_linkedit_data.end(),
                                     (char*)mapped_cache + functionStarts->dataoff(),
                                     (char*)mapped_cache + functionStarts->dataoff() + functionStartsSize);
        }

        // pointer align
        while ((linkEditSegCmd->fileoff() + new_linkedit_data.size()) % sizeof(pint_t))
            new_linkedit_data.push_back(0);

        const uint64_t newDataInCodeOffset = new_linkedit_data.size();
        uint32_t dataInCodeSize = 0;
        if ( dataInCode != NULL ) {
            // copy data-in-code info from original cache file to new mapped dylib file
            dataInCodeSize = dataInCode->datasize();
            new_linkedit_data.insert(new_linkedit_data.end(),
                                     (char*)mapped_cache + dataInCode->dataoff(),
                                     (char*)mapped_cache + dataInCode->dataoff() + dataInCodeSize);
        }

        std::vector<mach_o::trie::Entry> exports;
        if ( exportsTrieSize != 0 ) {
            const uint8_t* exportsStart = ((uint8_t*)mapped_cache) + exportsTrieOffset;
            const uint8_t* exportsEnd = &exportsStart[exportsTrieSize];
            mach_o::trie::parseTrie(exportsStart, exportsEnd, exports);
            exports.erase(std::remove_if(exports.begin(), exports.end(), NotReExportSymbol(reexportDeps)), exports.end());
        }

        // look for local symbol info in unmapped part of shared cache
        dyldCacheHeader<E>* header = (dyldCacheHeader<E>*)mapped_cache;
        macho_nlist<P>* localNlists = NULL;
        uint32_t localNlistCount = 0;
        const char* localStrings = NULL;
        const char* localStringsEnd = NULL;
        printf("mappingOffset: 0x%08x\n", header->mappingOffset());
        printf("offset of localSymbolsSize: %p\n", (void*)offsetof(dyld_cache_header, localSymbolsSize));
        if ( header->localSymbolsSize() > 0 && header->mappingOffset() > offsetof(dyld_cache_header,localSymbolsSize) ) {
            printf("localSymbolsOffset: %p\n", (void*)header->localSymbolsOffset());
            dyldCacheLocalSymbolsInfo<E>* localInfo = (dyldCacheLocalSymbolsInfo<E>*)(((uint8_t*)mapped_cache) + header->localSymbolsOffset());
            printf("localInfo entriesOffset(): 0x%08x\n", localInfo->entriesOffset());
            dyldCacheLocalSymbolEntry<E>* entries = (dyldCacheLocalSymbolEntry<E>*)(((uint8_t*)mapped_cache) + header->localSymbolsOffset() + localInfo->entriesOffset());
            macho_nlist<P>* allLocalNlists = (macho_nlist<P>*)(((uint8_t*)localInfo) + localInfo->nlistOffset());
            const uint32_t entriesCount = localInfo->entriesCount();
            printf("entriesCount: %d\n", entriesCount);
            for (uint32_t i=0; i < entriesCount; ++i) {
                printf("dylibOffset: 0x%08x\n", entries[i].dylibOffset());
                printf("textOffsetInCache: %p\n", (void*)textOffsetInCache);
                if ( entries[i].dylibOffset() == textOffsetInCache ) {
                    uint32_t localNlistStart = entries[i].nlistStartIndex();
                    localNlistCount = entries[i].nlistCount();
                    localNlists = &allLocalNlists[localNlistStart];
                    localStrings = ((char*)localInfo) + localInfo->stringsOffset();
                    localStringsEnd = &localStrings[localInfo->stringsSize()];
                    break;
                }
            }
        }
        // compute number of symbols in new symbol table
        const macho_nlist<P>* const mergedSymTabStart = (macho_nlist<P>*)(((uint8_t*)mapped_cache) + symtab->symoff());
        const macho_nlist<P>* const mergedSymTabend = &mergedSymTabStart[symtab->nsyms()];
        uint32_t newSymCount = symtab->nsyms();
        printf("nsyms: %d\n", symtab->nsyms());
        printf("symoff: 0x%08x\n", symtab->symoff());

        if ( localNlists != NULL ) {
            newSymCount = localNlistCount;
            for (const macho_nlist<P>* s = mergedSymTabStart; s != mergedSymTabend; ++s) {
                // skip any locals in cache
                if ( (s->n_type() & (N_TYPE|N_EXT)) == N_SECT )
                {
                    continue;
                }
                ++newSymCount;
            }
        }

        // add room for N_INDR symbols for re-exported symbols
        newSymCount += exports.size();

        // copy symbol entries and strings from original cache file to new mapped dylib file
        const char* mergedStringPoolStart = (char*)mapped_cache + symtab->stroff();
        const char* mergedStringPoolEnd = &mergedStringPoolStart[symtab->strsize()];

        // First count how many entries we need
        std::vector<macho_nlist<P>> newSymTab;
        newSymTab.reserve(newSymCount);

        std::vector<char> newSymNames;

        // first pool entry is always empty string
        newSymNames.push_back('\0');

        for (const macho_nlist<P>* s = mergedSymTabStart; s != mergedSymTabend; ++s) {
            // if we have better local symbol info, skip any locals here
            if ( (localNlists != NULL) && ((s->n_type() & (N_TYPE|N_EXT)) == N_SECT) ){
                continue;
            }
            macho_nlist<P> t = *s;
            t.set_n_strx((uint32_t)newSymNames.size());
            const char* symName = &mergedStringPoolStart[s->n_strx()];
            if ( symName > mergedStringPoolEnd )
                symName = "<corrupt symbol name>";
            newSymNames.insert(newSymNames.end(),
                               symName,
                               symName + (strlen(symName) + 1));
            newSymTab.push_back(t);
        }
        // <rdar://problem/16529213> recreate N_INDR symbols in extracted dylibs for debugger
        for (std::vector<mach_o::trie::Entry>::iterator it = exports.begin(); it != exports.end(); ++it) {
            macho_nlist<P> t;
            memset(&t, 0, sizeof(t));
            t.set_n_strx((uint32_t)newSymNames.size());
            t.set_n_type(N_INDR | N_EXT);
            t.set_n_sect(0);
            t.set_n_desc(0);
            newSymNames.insert(newSymNames.end(),
                               it->name,
                               it->name + (strlen(it->name) + 1));
            const char* importName = it->importName;
            if ( *importName == '\0' )
                importName = it->name;
            t.set_n_value(newSymNames.size());
            newSymNames.insert(newSymNames.end(),
                               importName,
                               importName + (strlen(importName) + 1));
            newSymTab.push_back(t);
        }
        if ( localNlists != NULL ) {
            // update load command to reflect new count of locals
            dynamicSymTab->set_ilocalsym((uint32_t)newSymTab.size());
            dynamicSymTab->set_nlocalsym(localNlistCount);
            // copy local symbols
            for (uint32_t i=0; i < localNlistCount; ++i) {
                const char* localName = &localStrings[localNlists[i].n_strx()];
                if ( localName > localStringsEnd )
                    localName = "<corrupt local symbol name>";
                macho_nlist<P> t = localNlists[i];
                t.set_n_strx((uint32_t)newSymNames.size());
                newSymNames.insert(newSymNames.end(),
                                   localName,
                                   localName + (strlen(localName) + 1));
                newSymTab.push_back(t);
            }
        }

        if ( newSymCount != newSymTab.size() ) {
            fprintf(stderr, "symbol count miscalculation\n");
            return -1;
        }

        //const uint64_t newStringPoolOffset = newIndSymTabOffset + dynamicSymTab->nindirectsyms()*sizeof(uint32_t);
        //macho_nlist<P>* const newSymTabStart = (macho_nlist<P>*)(((uint8_t*)mh) + newSymTabOffset);
        //char* const newStringPoolStart = (char*)mh + newStringPoolOffset;

        // pointer align
        while ((linkEditSegCmd->fileoff() + new_linkedit_data.size()) % sizeof(pint_t))
            new_linkedit_data.push_back(0);

        const uint64_t newSymTabOffset = new_linkedit_data.size();

        fixup_symtab(newSymTab, mapped_cache);

        // Copy sym tab
        for (macho_nlist<P>& sym : newSymTab) {
            uint8_t symData[sizeof(macho_nlist<P>)];
            memcpy(&symData, &sym, sizeof(sym));
            new_linkedit_data.insert(new_linkedit_data.end(), &symData[0], &symData[sizeof(macho_nlist<P>)]);
        }

        const uint64_t newIndSymTabOffset = new_linkedit_data.size();

        // Copy indirect symbol table
        const uint32_t* mergedIndSymTab = (uint32_t*)((char*)mapped_cache + dynamicSymTab->indirectsymoff());
        new_linkedit_data.insert(new_linkedit_data.end(),
                                 (char*)mergedIndSymTab,
                                 (char*)(mergedIndSymTab + dynamicSymTab->nindirectsyms()));

        const uint64_t newStringPoolOffset = new_linkedit_data.size();

        // pointer align string pool size
        while (newSymNames.size() % sizeof(pint_t))
            newSymNames.push_back('\0');

        new_linkedit_data.insert(new_linkedit_data.end(), newSymNames.begin(), newSymNames.end());

        // update load commands
        if ( functionStarts != NULL ) {
            functionStarts->set_dataoff((uint32_t)(newFunctionStartsOffset + linkEditSegCmd->fileoff()));
            functionStarts->set_datasize(functionStartsSize);
        }
        if ( dataInCode != NULL ) {
            dataInCode->set_dataoff((uint32_t)(newDataInCodeOffset + linkEditSegCmd->fileoff()));
            dataInCode->set_datasize(dataInCodeSize);
        }

        symtab->set_nsyms(newSymCount);
        printf("symtab offset: 0x%llx\n", (newSymTabOffset + linkEditSegCmd->fileoff()));
        symtab->set_symoff((uint32_t)(newSymTabOffset + linkEditSegCmd->fileoff()));
        symtab->set_stroff((uint32_t)(newStringPoolOffset + linkEditSegCmd->fileoff()));
        symtab->set_strsize((uint32_t)newSymNames.size());
        dynamicSymTab->set_extreloff(0);
        dynamicSymTab->set_nextrel(0);
        dynamicSymTab->set_locreloff(0);
        dynamicSymTab->set_nlocrel(0);
        dynamicSymTab->set_indirectsymoff((uint32_t)(newIndSymTabOffset + linkEditSegCmd->fileoff()));
        linkEditSegCmd->set_filesize(symtab->stroff()+symtab->strsize() - linkEditSegCmd->fileoff());
        linkEditSegCmd->set_vmsize( (linkEditSegCmd->filesize()+4095) & (-4096) );

        // <rdar://problem/17671438> Xcode 6 leaks in dyld_shared_cache_extract_dylibs
        for (std::vector<mach_o::trie::Entry>::iterator it = exports.begin(); it != exports.end(); ++it) {
            ::free((void*)(it->name));
        }


        return 0;
    }

};

static void make_dirs(const char* file_path)
{
    //printf("make_dirs(%s)\n", file_path);
    char dirs[strlen(file_path)+1];
    strcpy(dirs, file_path);
    char* lastSlash = strrchr(dirs, '/');
    if ( lastSlash == NULL )
        return;
    lastSlash[1] = '\0';
    struct stat stat_buf;
    if ( stat(dirs, &stat_buf) != 0 ) {
        char* afterSlash = &dirs[1];
        char* slash;
        while ( (slash = strchr(afterSlash, '/')) != NULL ) {
            *slash = '\0';
            ::mkdir(dirs, S_IRWXU | S_IRGRP|S_IXGRP | S_IROTH|S_IXOTH);
            //printf("mkdir(%s)\n", dirs);
            *slash = '/';
            afterSlash = slash+1;
        }
    }
}



template <typename A>
void dylib_maker(const void* mapped_cache, std::vector<uint8_t> &dylib_data, const std::vector<seg_info>& segments) {
    typedef typename A::P P;

    size_t  additionalSize  = 0;
    for(std::vector<seg_info>::const_iterator it=segments.begin(); it != segments.end(); ++it) {
        if ( strcmp(it->segName, "__LINKEDIT") != 0 )
            additionalSize += it->sizem;
    }

    std::vector<uint8_t> new_dylib_data;
    new_dylib_data.reserve(additionalSize);

    // Write regular segments into the buffer
    uint64_t                textOffsetInCache    = 0;
    for( std::vector<seg_info>::const_iterator it=segments.begin(); it != segments.end(); ++it) {


        if(strcmp(it->segName, "__TEXT") == 0 )
            textOffsetInCache = it->offset;

        //printf("segName=%s, offset=0x%llX, size=0x%0llX\n", it->segName, it->offset, it->sizem);
        // Copy all but the __LINKEDIT.  It will be copied later during the optimizer in to a temporary buffer but it would
        // not be efficient to copy it all now for each dylib.
        if (strcmp(it->segName, "__LINKEDIT") == 0 )
            continue;
        std::copy(((uint8_t*)mapped_cache)+it->offset, ((uint8_t*)mapped_cache)+it->offset+it->sizem, std::back_inserter(new_dylib_data));
    }

    // optimize linkedit
    std::vector<uint8_t> new_linkedit_data;
    new_linkedit_data.reserve(1 << 20);

    LinkeditOptimizer<A> linkeditOptimizer;
    macho_header<P>* mh = (macho_header<P>*)&new_dylib_data.front();
    linkeditOptimizer.optimize_loadcommands(mh, textOffsetInCache, mapped_cache, segments);
    linkeditOptimizer.optimize_linkedit(new_linkedit_data, textOffsetInCache, mapped_cache);

    new_dylib_data.insert(new_dylib_data.end(), new_linkedit_data.begin(), new_linkedit_data.end());

    // Page align file
    while (new_dylib_data.size() % 4096)
        new_dylib_data.push_back(0);

    dylib_data.insert(dylib_data.end(), new_dylib_data.begin(), new_dylib_data.end());
}

typedef __typeof(dylib_maker<x86>) dylib_maker_func;
typedef void (^progress_block)(unsigned current, unsigned total);

class SharedCacheExtractor;
struct SharedCacheDylibExtractor {
    SharedCacheDylibExtractor(const char* name, std::vector<seg_info> segInfo)
        : name(name), segInfo(segInfo) { }

    void extractCache(SharedCacheExtractor& context);

    const char*                     name;
    const std::vector<seg_info>     segInfo;
    int                             result = 0;
};

struct SharedCacheExtractor {
    SharedCacheExtractor(const NameToSegments& map,
                         const char* extraction_root_path,
                         dylib_maker_func* dylib_create_func,
                         void* mapped_cache,
                         progress_block progress)
        : map(map), extraction_root_path(extraction_root_path),
          dylib_create_func(dylib_create_func), mapped_cache(mapped_cache),
          progress(progress) {

      extractors.reserve(map.size());
      for (auto it : map)
          extractors.emplace_back(it.first, it.second);

        // Limit the number of open files.  16 seems to give better performance than higher numbers.
        sema = dispatch_semaphore_create(16);
    }
    int extractCaches();

    static void extractCache(void *ctx, size_t i);

    const NameToSegments&                   map;
    std::vector<SharedCacheDylibExtractor>  extractors;
    dispatch_semaphore_t                    sema;
    const char*                             extraction_root_path;
    dylib_maker_func*                       dylib_create_func;
    void*                                   mapped_cache;
    progress_block                          progress;
    std::atomic_int                         count = { 0 };
};

int SharedCacheExtractor::extractCaches() {
    dispatch_queue_t process_queue = dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_LOW, 0);
    dispatch_apply_f(map.size(), process_queue,
                     this, extractCache);

    int result = 0;
    for (const SharedCacheDylibExtractor& extractor : extractors) {
        if (extractor.result != 0) {
            result = extractor.result;
            break;
        }
    }
    return result;
}

void SharedCacheExtractor::extractCache(void *ctx, size_t i) {
    SharedCacheExtractor& context = *(SharedCacheExtractor*)ctx;
    dispatch_semaphore_wait(context.sema, DISPATCH_TIME_FOREVER);
    context.extractors[i].extractCache(context);
    dispatch_semaphore_signal(context.sema);
}

void SharedCacheDylibExtractor::extractCache(SharedCacheExtractor &context) {

    char    dylib_path[PATH_MAX];
    strcpy(dylib_path, context.extraction_root_path);
    strcat(dylib_path, "/");
    strcat(dylib_path, name);

    //printf("%s with %lu segments\n", dylib_path, it->second.size());
    // make sure all directories in this path exist
    make_dirs(dylib_path);

    // open file, create if does not already exist
    int fd = ::open(dylib_path, O_CREAT | O_TRUNC | O_EXLOCK | O_RDWR, 0644);
    if ( fd == -1 ) {
        fprintf(stderr, "can't open or create dylib file %s, errnor=%d\n", dylib_path, errno);
        result = -1;
        return;
    }

    std::vector<uint8_t> vec;
    context.dylib_create_func(context.mapped_cache, vec, segInfo);
    context.progress(context.count++, (unsigned)context.map.size());

    // Write file data
    if( write(fd, &vec.front(), vec.size()) == -1) {
        fprintf(stderr, "error writing, errnor=%d\n", errno);
        result = -1;
    }

    close(fd);
}

static int sharedCacheIsValid(const void* mapped_cache, uint64_t size) {
    // First check that the size is good.
    // Note the shared cache may not have a codeSignatureSize value set so we need to first make
    // sure we have space for the CS_SuperBlob, then later crack that to check for the size of the rest.
    const DyldSharedCache* dyldSharedCache = (DyldSharedCache*)mapped_cache;
    uint64_t requiredSizeForCSSuperBlob = dyldSharedCache->header.codeSignatureOffset + sizeof(CS_SuperBlob);
    const dyld_cache_mapping_info* mappings = (dyld_cache_mapping_info*)((uint8_t*)mapped_cache + dyldSharedCache->header.mappingOffset);
    if ( requiredSizeForCSSuperBlob > size ) {
        fprintf(stderr, "Error: dyld shared cache size 0x%08llx is less than required size of 0x%08llx.\n", size, requiredSizeForCSSuperBlob);
        return -1;
    }

    // Now see if the code signatures are valid as that tells us the pages aren't corrupt.
    // First find all of the regions of the shared cache we computed cd hashes
    std::vector<std::pair<uint64_t, uint64_t>> sharedCacheRegions;
    sharedCacheRegions.emplace_back(std::make_pair(mappings[0].fileOffset, mappings[0].fileOffset + mappings[0].size));
    sharedCacheRegions.emplace_back(std::make_pair(mappings[1].fileOffset, mappings[1].fileOffset + mappings[1].size));
    sharedCacheRegions.emplace_back(std::make_pair(mappings[2].fileOffset, mappings[2].fileOffset + mappings[2].size));
    if (dyldSharedCache->header.localSymbolsSize)
        sharedCacheRegions.emplace_back(std::make_pair(dyldSharedCache->header.localSymbolsOffset, dyldSharedCache->header.localSymbolsOffset + dyldSharedCache->header.localSymbolsSize));
    size_t inBbufferSize = 0;
    for (auto& sharedCacheRegion : sharedCacheRegions)
        inBbufferSize += (sharedCacheRegion.second - sharedCacheRegion.first);

    // Now take the cd hash from the cache itself and validate the regions we found.
    uint8_t* codeSignatureRegion = (uint8_t*)mapped_cache + dyldSharedCache->header.codeSignatureOffset;
    CS_SuperBlob* sb = reinterpret_cast<CS_SuperBlob*>(codeSignatureRegion);
    if (sb->magic != htonl(CSMAGIC_EMBEDDED_SIGNATURE)) {
        fprintf(stderr, "Error: dyld shared cache code signature magic is incorrect.\n");
        return -1;
    }

    size_t sbSize = ntohl(sb->length);
    uint64_t requiredSizeForCS = dyldSharedCache->header.codeSignatureOffset + sbSize;
    if ( requiredSizeForCS > size ) {
        fprintf(stderr, "Error: dyld shared cache size 0x%08llx is less than required size of 0x%08llx.\n", size, requiredSizeForCS);
        return -1;
    }

    // Find the offset to the code directory.
    CS_CodeDirectory* cd = nullptr;
    for (unsigned i =0; i != sb->count; ++i) {
        if (ntohl(sb->index[i].type) == CSSLOT_CODEDIRECTORY) {
            cd = (CS_CodeDirectory*)(codeSignatureRegion + ntohl(sb->index[i].offset));
            break;
        }
    }

    if (!cd) {
        fprintf(stderr, "Error: dyld shared cache code signature directory is missing.\n");
        return -1;
    }

    if ( (uint8_t*)cd > (codeSignatureRegion + sbSize) ) {
        fprintf(stderr, "Error: dyld shared cache code signature directory is out of bounds.\n");
        return -1;
    }

    if ( cd->magic != htonl(CSMAGIC_CODEDIRECTORY) ) {
        fprintf(stderr, "Error: dyld shared cache code signature directory magic is incorrect.\n");
        return -1;
    }

    uint32_t pageSize = 1 << cd->pageSize;
    uint32_t slotCountFromRegions = (uint32_t)((inBbufferSize + pageSize - 1) / pageSize);
    if ( ntohl(cd->nCodeSlots) < slotCountFromRegions ) {
        fprintf(stderr, "Error: dyld shared cache code signature directory num slots is incorrect.\n");
        return -1;
    }

    uint32_t dscDigestFormat = kCCDigestNone;
    switch (cd->hashType) {
        case CS_HASHTYPE_SHA1:
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"
            dscDigestFormat = kCCDigestSHA1;
#pragma clang diagnostic pop
            break;
        case CS_HASHTYPE_SHA256:
            dscDigestFormat = kCCDigestSHA256;
            break;
        default:
            break;
    }

    if (dscDigestFormat != kCCDigestNone) {
        const uint64_t csPageSize = 1 << cd->pageSize;
        size_t   hashOffset = ntohl(cd->hashOffset);
        uint8_t* hashSlot = (uint8_t*)cd + hashOffset;
        uint8_t cdHashBuffer[cd->hashSize];

        // Skip local symbols for now as those aren't being codesign correctly right now.
        size_t inBbufferSize = 0;
        for (auto& sharedCacheRegion : sharedCacheRegions) {
            if (sharedCacheRegion.first == dyldSharedCache->header.localSymbolsOffset)
                continue;
            inBbufferSize += (sharedCacheRegion.second - sharedCacheRegion.first);
        }
        uint32_t slotCountToProcess = (uint32_t)((inBbufferSize + pageSize - 1) / pageSize);

        for (unsigned i = 0; i != slotCountToProcess; ++i) {
            // Skip data pages as those may have been slid by ASLR in the extracted file
            uint64_t fileOffset = i * csPageSize;
            if ( (fileOffset >= mappings[1].fileOffset) && (fileOffset < (mappings[1].fileOffset + mappings[1].size)) )
                continue;

            CCDigest(dscDigestFormat, (uint8_t*)mapped_cache + fileOffset, (size_t)csPageSize, cdHashBuffer);
            uint8_t* cacheCdHashBuffer = hashSlot + (i * cd->hashSize);
            if (memcmp(cdHashBuffer, cacheCdHashBuffer, cd->hashSize) != 0)  {
                fprintf(stderr, "Error: dyld shared cache code signature for page %d is incorrect.\n", i);
                return -1;
            }
        }
    }
    return 0;
}

int dyld_shared_cache_extract_dylibs_progress(const char* shared_cache_file_path, const char* extraction_root_path,
                                              progress_block progress)
{
    struct stat statbuf;
    if (stat(shared_cache_file_path, &statbuf)) {
        fprintf(stderr, "Error: stat failed for dyld shared cache at %s\n", shared_cache_file_path);
        return -1;
    }

    int cache_fd = open(shared_cache_file_path, O_RDONLY);
    if (cache_fd < 0) {
        fprintf(stderr, "Error: failed to open shared cache file at %s\n", shared_cache_file_path);
        return -1;
    }

    void* mapped_cache = mmap(NULL, (size_t)statbuf.st_size, PROT_READ, MAP_PRIVATE, cache_fd, 0);
    if (mapped_cache == MAP_FAILED) {
        fprintf(stderr, "Error: mmap() for shared cache at %s failed, errno=%d\n", shared_cache_file_path, errno);
        return -1;
    }

    close(cache_fd);

    // instantiate arch specific dylib maker
    dylib_maker_func* dylib_create_func = nullptr;
    if ( strcmp((char*)mapped_cache, "dyld_v1    i386") == 0 )
        dylib_create_func = dylib_maker<x86>;
    else if ( strcmp((char*)mapped_cache, "dyld_v1  x86_64") == 0 )
        dylib_create_func = dylib_maker<x86_64>;
    else if ( strcmp((char*)mapped_cache, "dyld_v1 x86_64h") == 0 )
        dylib_create_func = dylib_maker<x86_64>;
    else if ( strcmp((char*)mapped_cache, "dyld_v1   armv5") == 0 )
        dylib_create_func = dylib_maker<arm>;
    else if ( strcmp((char*)mapped_cache, "dyld_v1   armv6") == 0 )
        dylib_create_func = dylib_maker<arm>;
    else if ( strcmp((char*)mapped_cache, "dyld_v1   armv7") == 0 )
        dylib_create_func = dylib_maker<arm>;
    else if ( strncmp((char*)mapped_cache, "dyld_v1  armv7", 14) == 0 )
        dylib_create_func = dylib_maker<arm>;
    else if ( strcmp((char*)mapped_cache, "dyld_v1   arm64") == 0 )
        dylib_create_func = dylib_maker<arm64>;
#if SUPPORT_ARCH_arm64e
    else if ( strcmp((char*)mapped_cache, "dyld_v1  arm64e") == 0 )
        dylib_create_func = dylib_maker<arm64>;
#endif
#if SUPPORT_ARCH_arm64_32
    else if ( strcmp((char*)mapped_cache, "dyld_v1arm64_32") == 0 )
        dylib_create_func = dylib_maker<arm64_32>;
#endif
    else {
        fprintf(stderr, "Error: unrecognized dyld shared cache magic.\n");
        munmap(mapped_cache, (size_t)statbuf.st_size);
        return -1;
    }

    // Verify that the cache isn't corrupt.
    if (int result = sharedCacheIsValid(mapped_cache, (uint64_t)statbuf.st_size)) {
        munmap(mapped_cache, (size_t)statbuf.st_size);
        return result;
    }

    // iterate through all images in cache and build map of dylibs and segments
    __block NameToSegments  map;
    int                     result = 0;

    result = dyld_shared_cache_iterate(mapped_cache, (uint32_t)statbuf.st_size, ^(const dyld_shared_cache_dylib_info* dylibInfo, const dyld_shared_cache_segment_info* segInfo) {
        map[dylibInfo->path].push_back(seg_info(segInfo->name, segInfo->fileOffset, segInfo->fileSize));
    });

    if(result != 0) {
        fprintf(stderr, "Error: dyld_shared_cache_iterate_segments_with_slide failed.\n");
        munmap(mapped_cache, (size_t)statbuf.st_size);
        return result;
    }

    // for each dylib instantiate a dylib file
    SharedCacheExtractor extractor(map, extraction_root_path, dylib_create_func, mapped_cache, progress);
    result = extractor.extractCaches();

    munmap(mapped_cache, (size_t)statbuf.st_size);
    return result;
}



int dyld_shared_cache_extract_dylibs(const char* shared_cache_file_path, const char* extraction_root_path)
{
    return dyld_shared_cache_extract_dylibs_progress(shared_cache_file_path, extraction_root_path,
                                                     ^(unsigned , unsigned) {} );
}


#if 0
// test program
#include <stdio.h>
#include <stddef.h>
#include <dlfcn.h>


typedef int (*extractor_proc)(const char* shared_cache_file_path, const char* extraction_root_path,
                              void (^progress)(unsigned current, unsigned total));

int main(int argc, const char* argv[])
{
    if ( argc != 3 ) {
        fprintf(stderr, "usage: dsc_extractor <path-to-cache-file> <path-to-device-dir>\n");
        return 1;
    }

    //void* handle = dlopen("/Volumes/my/src/dyld/build/Debug/dsc_extractor.bundle", RTLD_LAZY);
    void* handle = dlopen("/Applications/Xcode.app/Contents/Developer/Platforms/iPhoneOS.platform/usr/lib/dsc_extractor.bundle", RTLD_LAZY);
    if ( handle == NULL ) {
        fprintf(stderr, "dsc_extractor.bundle could not be loaded\n");
        return 1;
    }

    extractor_proc proc = (extractor_proc)dlsym(handle, "dyld_shared_cache_extract_dylibs_progress");
    if ( proc == NULL ) {
        fprintf(stderr, "dsc_extractor.bundle did not have dyld_shared_cache_extract_dylibs_progress symbol\n");
        return 1;
    }

    int result = (*proc)(argv[1], argv[2], ^(unsigned c, unsigned total) { printf("%d/%d\n", c, total); } );
    fprintf(stderr, "dyld_shared_cache_extract_dylibs_progress() => %d\n", result);
    return 0;
}


#endif




