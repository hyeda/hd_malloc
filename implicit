/*
 * mm-naive.c - 가장 빠르지만, 메모리 효율이 가장 낮은 malloc 패키지.
 * 
 * 이 단순한 방법에서는, 메모리 블록을 할당할 때 단순히 brk 포인터를 증가시키기만 합니다.
 * 블록은 순수한 데이터(payload)로만 이루어져 있습니다. 헤더나 푸터는 없습니다.
 * 블록은 결합(coalescing)되거나 재사용되지 않습니다. 
 * Realloc은 mm_malloc과 mm_free를 직접 사용하여 구현됩니다.
 *
 * 학생들에게 주의사항: 이 주석을 여러분의 솔루션에 대한 상위 수준의 설명을 포함하는 주석으로 교체하세요.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"


team_t team = {
    /* Team name */
    "happy_hyeda",
    /* First member's full name */
    "Kim hyeda",
    /* First member's email address */
    "hyeda@gmail.com",
    /* Second member's full name (leave blank if none) */
    "eunsang dalgyu",
    /* Second member's email address (leave blank if none) */
    "dd@gmail.com"
};

int mm_init(void);
static void *extend_heap(size_t words);
void *mm_malloc(size_t req_size);
static void *find_fit(size_t alloc_size);
static void place(void *bp, size_t alloc_size);
void mm_free(void *bp);
static void *coalesce(void *bp);
void *mm_realloc(void *old_bp, size_t req_size);


//정렬 기준, 64비트 시스템은 보통 시작주소를 8바이트의 배수가 되도록 정렬함.
// #define ALIGNMENT 8

// #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) 
// // size를 가까운 8의 배수로 올림처리 함. 메모리 블록의 크기가 항상 8바이트의 배수로 정렬되게 하는역할
// // 0x7은 111이므로 and연산을 통해서  마지막 3비트가 존재했다면 올림처리가 되면서 8의 배수로 설정 되는 것이다.

// // 자료형의 크기를 정렬된 크기로 계산하여 저장한 값. 위에 ALIGN매크로 사용해서 정렬된 크기로 맞춰줌.
// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 가용 리스트 조작을 위한 기본 상수 및 매크로 정의
#define WSIZE 4 // 워드나 헤더,푸터
#define DSIZE 8 // 더블워드
#define CHUNKSIZE (1<<12) //초기 가용 블록과 힙 확장을 위한 기본 크기

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc)) // 블록의 크기(8바이트 정렬된값)와 할당상태(1비트)를 하나의 값으로 저장하기 위해 사용됨. 헤더와 푸터에 이 정보를 넣음.

#define GET(p)  (*(unsigned int*)(p)) // 포인터를 사용해 메모리의 특정 위치에 값을 읽어온다. // 일반포인터 p를 unsigned int 포인터로 변환 하는 작업.
//역참조(dereference) 연산을 통해 p가 가리키는 메모리 위치에 있는 값을 읽는다. 이 값은 unsigned int로 처리
#define PUT(p, val)  (*(unsigned int*)(p) = (val)) // 얘는 값을 써 넣는다.

#define GET_SIZE(p)  (GET(p) & ~0x7) //~0x7은 1111 1000임.그래서 마지막 3비트만 버리는 용도. // 블록 전체 크기
#define GET_ALLOC(p)  (GET(p) & 0x1) //마지막 1비트만 가져오는 용도.

//block ptr = 실제 데이터를 저장하는 위치를 가리키는 포인터
#define HDRP(bp)    ((char*)(bp) - WSIZE) // bp보다 1워드 앞에 헤더포인트가 있음.!
#define FTRP(bp)    ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // GET_SIZE(HDRP(bp))는 헤더와 푸터를 포함한 전체 블록크기(헤더,페이로드,푸터)를 의미함.

#define NEXT_BLKP(bp)    ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE)) 
// 헤더의 위치 계산해서, 헤더에서 블록의 전체 크기를 읽어온다. 다음 블럭의 시작 주소 계산
#define PREV_BLKP(bp)    ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE)) 
// 이전 블럭의 푸터 위치 계산해서 전 블록의 전체 크기 읽어온다. 그다음 현재 위치에서 전 블록 크기 빼면 전 블럭의 시작 주소로 감.


static char *heap_listp; // 힙에서 관리되는 블록 리스트의 시작 포인트

//최초 가용 블록으로 힙 생성하기.
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) // 새로 할당된 힙 영역의 시작 주소를 저장하고 가리킴.
    //mem_sbrk가 메모리를 할당하고 할당된 메모리 영역의 시작 주소를 반환하는 애임. 반환값이 -1이면 메모리 확장에 실패한것.
        return -1;
    PUT(heap_listp, 0); // 첫부분에 0을 넣음. 이부분은 나중에 필요하지 않은 패딩 공간, 정렬을 맞추기 위해 필요하다.
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 두번째 워드 위치에 블록 크기 8 바이트와 할당 상태를 저장함. 이부분이 프롤로그 블록의 헤더임. 힙의 시작을 표시
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 세번째 워드 위치에도 똑같은 내용. 이부분이 프롤로그 블록의 푸터임.
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // 마지막 워드 위치에 블록 크기 0과 할당 상태 저장. 에필로그 블록. 힙의 끝을 나타내는 역할
    heap_listp += (2*WSIZE); // 이동 전에는 프롤로그 블록의 헤더를 가리키고 있다가 후에는 프롤로그 블록 다음에 올 첫번째 실제 가용 블록의 시작 주소를 가리키게 됨.

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) // 초기 힙 확장 크기 2의 12승 / 4 = 2의 10승 개의 워드 크기만큼 확장하겠다. 
        return -1;
    return 0;
}
//사이즈 만큼 확장해주는 함수; 성공시-> 새로 할당된 블록의 시작 주소 반환. 실패하면 NULL 
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 0이 False 짝수, 1이 True 홀수 -> 짝수 워드 단위로 관리하는게 효율적.
    if ((long)(bp = mem_sbrk(size)) == -1) // mem_sbrk 에서 반환된 값을 정수(큰 정수형 long)로 변환해서 -1인지 확인하기 위함이다.
        return NULL;

    PUT(HDRP(bp), PACK(size, 0)); // 블록의 헤더 위치에 size만큼 가용상태를 기록
    PUT(FTRP(bp), PACK(size, 0));  // 푸터에도 똑같이!
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 다음 블록의 헤더에 에필로그 블록을 기록함.

    return coalesce(bp); 
}



/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t req_size)
{
    size_t alloc_size;
    size_t extendsize;
    char *bp;

    if (req_size == 0)
        return NULL; // 사이즈가 0이면 할당할 필요가 없으니 NULL 반환
    
    if (req_size <= DSIZE) // 요청한 크기가 너무 작으면 최소 8바이트 할당
        alloc_size = 2*DSIZE; // 헤더 4, 페이로드 최소 8, 푸터4 = 최소16

    else
        alloc_size = DSIZE * ((req_size + (DSIZE) + (DSIZE-1)) / DSIZE); // 요청한 크기가 더 크면 8의 배수로 크기 맞춰서 정렬

    if ((bp = find_fit(alloc_size)) != NULL) { // 빈공간 주소 bp에 저장
        place(bp, alloc_size); // 그 자리에 할당
        return bp;
    }
    extendsize = MAX(alloc_size, CHUNKSIZE); //만약 적당한 빈 공간이 없으면, 새로운 메모리 공간을 힙에 추가 함.
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) // 최소 요청한 크기 or 정해진 기본크기chunksize 만큼 확장 
        return NULL; // 실패하면 NULL 반환
    place(bp, alloc_size);
    return bp;
}

//빈공간을 찾아주는 함수, 요청한 크기만큼 맞는 빈 공간이 있으면 그 공간의 주소를 반환
static void *find_fit(size_t alloc_size) // malloc에서 이미 요청한 크기에 헤더와 푸터를 포함한 크기를 alloc에 넣음.
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { // get_size == 0(에필로그 블록)이 될때 까지 반복해서 탐색하라는 의미. 
        if (!GET_ALLOC(HDRP(bp)) && (alloc_size <= GET_SIZE(HDRP(bp)))) { // 할당되지 않고, 블록크기가 요청한 크기보다 크거나 같은지.
            return bp;
        }
    }
    return NULL;
}

//요청된 블록을 할당하는 함수. 블록 할당하고 남은 공간이 충분히 크면 분할하는 로직도 포함함.
static void place(void *bp, size_t alloc_size) 
{
    size_t block_size = GET_SIZE(HDRP(bp)); 

    if ((block_size - alloc_size) >= (2*DSIZE)) { // 블럭에서 할당된 크기를 뺐는데도 최소 한 블럭 만들수 있는 크기 나오면 분할
        PUT(HDRP(bp), PACK(alloc_size, 1)); // 헤더에 할당된 사이즈 할당
        PUT(FTRP(bp), PACK(alloc_size, 1)); // 푸터에도 똑같이 저장
        bp = NEXT_BLKP(bp); // 다음 블럭 포인트, 할당된 사이즈 계산해서 옮기는거임.
        PUT(HDRP(bp), PACK(block_size-alloc_size, 0)); // 남은 크기 정보에 넣어주고 가용상태로 만들기.
        PUT(FTRP(bp), PACK(block_size-alloc_size, 0)); // 푸터에도 똑같이.

    } else { // 하나 만들 사이즈 안나오면 그냥 할당만 해주기.
        PUT(HDRP(bp), PACK(block_size, 1)); 
        PUT(FTRP(bp), PACK(block_size, 1));
    }
}

// 동적 메모리 할당에서 블록을 해제하는 함수
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); //블록 크기 가져오기.

    PUT(HDRP(bp), PACK(size, 0)); // 헤더에 블록크기와 가용상태를 기록함.
    PUT(FTRP(bp), PACK(size, 0)); // 푸터에도
    coalesce(bp); // 위에 설명함.
}

// 새로 만든 블록이 인접 가용 블록들과 병합 가능한지 확인하고 가능하면 합치고 그 시작 주소를 반환함.
static void *coalesce(void *bp) // 코얼레스 = 합체하다.
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 앞블럭의 가용상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 뒷블럭의 가용상태
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블럭의 크기

    if (prev_alloc && next_alloc ) { // 둘다 할당 된 상태
        return bp;

    } else if (prev_alloc && !next_alloc){ // 뒷블럭만 가용상태
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 사이즈를 뒷블럭 크기만큼 키움.
        PUT(HDRP(bp), PACK(size, 0)); // 헤더 푸터 정보 갱신
        PUT(FTRP(bp), PACK(size, 0));

    } else if (!prev_alloc && next_alloc){ // 앞블럭만 가용상태
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); 
        PUT(FTRP(bp), PACK(size, 0)); 
        bp = PREV_BLKP(bp); // 헤더는 앞블럭의 헤더위치로 옮겨 줘야 함.
        PUT(HDRP(bp), PACK(size, 0)); // 그 다음 헤더 정보 갱신

    } else { 
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 앞 뒤 블록 둘다 가용상태
        bp = PREV_BLKP(bp); // 헤더를 앞블럭의 헤더위치로 옮겨 줘야 함.
        PUT(HDRP(bp), PACK(size, 0)); 
        PUT(FTRP(bp), PACK(size, 0));
    }
    return bp;
}

// 메모리 블록의 크기를 변경할 때 사용됨. -> 기존 데이터를 새로운 블록으로 복사한 후 이전 블록을 해제함.
void *mm_realloc(void *old_bp, size_t req_size) 
{
    void *new_bp;
    size_t copySize;
    
    new_bp = mm_malloc(req_size); 
    if (new_bp == NULL) // 할당 실패! 
      return NULL; 

    copySize = GET_SIZE(HDRP(old_bp)) - DSIZE; // 기존 블록의 크기에서 헤더와 푸터 뺀 값을 복사, 새 블록으로 복사할 데이터의 크기
    // 새로운 블록을 할당할 땐 새로운 헤더와 푸터가 필요하니까, 데이터만 복사함.

    if (req_size < copySize) // 요청한 크기(이것도 데이터만의 크기임)가 현재 블록크기보다 작으면 요청된 크기로 맞춰줌.
      copySize = req_size;

    memcpy(new_bp, old_bp, copySize); //새 블록에 기존 블록의 데이터를 카피함.
    mm_free(old_bp);
    return new_bp;
}
