/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
  /* Team name */
  " teem",
  /* First member's full name */
  " Mason Ferrell",
  /* First member's email address */
  "thfe9880@colorado.edu",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};

/////////////////////////////////////////////////////////////////////////////
// Constants and macros
//
// These correspond to the material in Figure 9.43 of the text
// The macros have been turned into C++ inline functions to
// make debugging code easier.
//
/////////////////////////////////////////////////////////////////////////////
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

static inline int MAX(int x, int y) {
  return x > y ? x : y;
}

//
// Pack a size and allocated bit into a word
// We mask of the "alloc" field to insure only
// the lower bit is used
//
static inline uint32_t PACK(uint32_t size, int alloc) {
  return ((size) | (alloc & 0x1));
}

//
// Read and write a word at address p
//
static inline uint32_t GET(void *p) { return  *(uint32_t *)p; }
static inline void PUT( void *p, uint32_t val)
{
  *((uint32_t *)p) = val;
}

//
// Read the size and allocated fields from address p
//
static inline uint32_t GET_SIZE( void *p )  { 
  return GET(p) & ~0x7;
}

static inline int GET_ALLOC( void *p  ) {
  return GET(p) & 0x1;
}

//
// Given block ptr bp, compute address of its header and footer
//
static inline void *HDRP(void *bp) {

  return ( (char *)bp) - WSIZE;
}
static inline void *FTRP(void *bp) {
  return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

//
// Given block ptr bp, compute address of next and previous blocks
//
static inline void *NEXT_BLKP(void *bp) {
  return  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
}

static inline void* PREV_BLKP(void *bp){
  return  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));
}

/////////////////////////////////////////////////////////////////////////////
//
// Global Variables
//

static char *heap_listp;  /* pointer to first block */  
static char *temp; //I added this to hold the heap list pointer sometimes

//
// function prototypes for internal helper routines
//
static void *extend_heap(uint32_t words);
static void place(void *bp, uint32_t asize);
static void *find_fit(uint32_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

//
// mm_init - Initialize the memory manager 
//
int mm_init(void) 
{
    //initial empty heap
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1)
    {
        return -1;
    }
    PUT(heap_listp, 0);     //Alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    //Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    //Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));    //Epilogue header
    heap_listp += (2*WSIZE);
    temp = heap_listp;
    //increase empty heap by CHUNKSIZE bytes
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}


//
// extend_heap - Extend heap with free block and return its block pointer
//
static void *extend_heap(uint32_t words) 
{
    char *blockpointer;
    size_t wordSize;
    //Allocate an even number of words to maintain alignment
    wordSize = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(blockpointer = mem_sbrk(wordSize)) == -1)
    {
        return NULL;
    }
    // Creating the free block header/footer and the epilogue header
    PUT(HDRP(blockpointer), PACK(wordSize, 0));   //block header
    PUT(FTRP(blockpointer), PACK(wordSize, 0));   //block footer
    PUT(HDRP(NEXT_BLKP(blockpointer)), PACK(0, 1));   //epilogue header
    
    // Coalesce if the previous block was free
    return coalesce(blockpointer);
}


//
// Practice problem 9.8
//
// find_fit - Find a fit for a block with asize bytes 
//
static void *find_fit(uint32_t asize)
{
    char *intialPointer = temp;
    
    for ( ; GET_SIZE(HDRP(temp)) > 0; temp = NEXT_BLKP(temp))
    {
        if (!GET_ALLOC(HDRP(temp)) && (asize <= GET_SIZE(HDRP(temp))))
        {
            return temp;
        }
    }
    // search from the beginning of the list all the way to old rover 
    for (temp = heap_listp; temp < intialPointer; temp = NEXT_BLKP(temp))
    {
        if (!GET_ALLOC(HDRP(temp)) && (asize <= GET_SIZE(HDRP(temp))))
        { 
            return temp;
        }
    }
    return NULL;
}

// 
// mm_free - Free a block 
//
void mm_free(void *bp)
{
    size_t addressSize = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(addressSize, 0));
    PUT(FTRP(bp), PACK(addressSize, 0));
    coalesce(bp);
}

//
// coalesce - boundary tag coalescing. Return ptr to coalesced block
//
static void *coalesce(void *bp) 
{
    size_t addressSize = GET_SIZE(HDRP(bp));
    size_t nextAlloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t previousAlloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    //check the different address sizes
    if(previousAlloc && nextAlloc)
    {
        return bp;
    }
        else if(!previousAlloc && nextAlloc)
    {
        addressSize =addressSize+ GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(addressSize, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(addressSize, 0));
        bp = PREV_BLKP(bp);
    }
    else if(previousAlloc && !nextAlloc)
    {
        addressSize =addressSize+GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(addressSize, 0));
        PUT(FTRP(bp), PACK(addressSize, 0));
    }
    else
    {
        addressSize=addressSize+GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(addressSize, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(addressSize, 0));
        bp = PREV_BLKP(bp);
    }
    if ((temp > (char *)bp) && (temp < (char *)NEXT_BLKP(bp)))
    {
        temp = bp;
    }
    return bp;
}

//
// mm_malloc - Allocate a block with at least size bytes of payload 
//
void *mm_malloc(uint32_t size) 
{
    size_t addressSize;
    size_t increaseSize;
    char *blockPointer;
    
    if(size == 0)
    {
        return NULL;
    }
    if(size <= DSIZE)
    {
        addressSize = 2*DSIZE;
    }
    else
    {
        addressSize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
    
    if ((blockPointer = find_fit(addressSize)) != NULL)
    {
        place(blockPointer, addressSize);
        return blockPointer;
    }
    increaseSize = MAX(addressSize, CHUNKSIZE);
    if((blockPointer = extend_heap(increaseSize/WSIZE)) == NULL)
    {
        return NULL;
    }
    place(blockPointer, addressSize);
    return blockPointer;
} 

//
//
// Practice problem 9.9
//
// place - Place block of asize bytes at start of free block bp 
//         and split if remainder would be at least minimum block size
//
static void place(void *bp, uint32_t asize)
{
    size_t headerfooterSize = GET_SIZE(HDRP(bp));
    if((headerfooterSize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(headerfooterSize-asize, 0));
        PUT(FTRP(bp), PACK(headerfooterSize-asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(headerfooterSize, 1));
        PUT(FTRP(bp), PACK(headerfooterSize, 1));
    }
}


//
// mm_realloc -- implemented for you
//
void *mm_realloc(void *ptr, uint32_t size)
{
    void *newp;
    uint32_t asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // making sure we have the proper amount of overhead somehow
    uint32_t isize = GET_SIZE(HDRP(ptr));
    if(isize > asize)
    {
        return ptr;
    } 
    else
    {
        uint32_t nextblocksize = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));

        if((!next_alloc) && ((asize - isize) < nextblocksize) && (isize - asize) >= (2 * DSIZE))
        {
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            newp = NEXT_BLKP(ptr);
            PUT(HDRP(newp), PACK(nextblocksize - (asize - isize), 0));
            PUT(FTRP(newp), PACK(nextblocksize - (asize - isize), 0));
            return ptr;
         } 
         else 
         { 
             size_t allocate = MAX(618784, size);
             newp = mm_malloc(allocate);
             if (newp == NULL) {
                 printf("ERROR: mm_malloc failed in mm_realloc\n");
                 exit(1);
             }
             memcpy(newp, ptr, isize);
             mm_free(ptr);
             return newp; 
          }
  } 
}

//
// mm_checkheap - Check the heap for consistency 
//
void mm_checkheap(int verbose) 
{
  //
  // This provided implementation assumes you're using the structure
  // of the sample solution in the text. If not, omit this code
  // and provide your own mm_checkheap
  //
  void *bp = heap_listp;
  
  if (verbose) {
    printf("Heap (%p):\n", heap_listp);
  }

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
    printf("Bad prologue header\n");
  }
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose)  {
      printblock(bp);
    }
    checkblock(bp);
  }
     
  if (verbose) {
    printblock(bp);
  }

  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
    printf("Bad epilogue header\n");
  }
}
static void printblock(void *bp) 
{
  uint32_t hsize, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));  
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));  
    
  if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

  printf("%p: header: [%d:%c] footer: [%d:%c]\n",
     bp, 
     (int) hsize, (halloc ? 'a' : 'f'), 
     (int) fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
  if ((uintptr_t)bp % 8) {
    printf("Error: %p is not doubleword aligned\n", bp);
  }
  if (GET(HDRP(bp)) != GET(FTRP(bp))) {
    printf("Error: header does not match footer\n");
  }
}