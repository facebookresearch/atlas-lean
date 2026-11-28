# Bottom-up heap construction takes linear time

*[Bottom-up heap construction](build-heap.md)* turns an arbitrary array $a$ of length $n$ over a linearly ordered type into a [binary min-heap](min-heap.md). It [sifts down](sift-down.md) every internal position $i = \lfloor n/2 \rfloor - 1, \dots, 1, 0$ in turn, from the last internal node back to the root, using 0-indexed level-order storage. Its [timed version](build-heap-2.md) counts value comparisons and array swaps as [timed sift-down](sift-down-2.md) does. The [height](heap-height.md) of an index $i$ in the level-order binary tree with $n$ nodes is $\lfloor \log_2 \lfloor n/(i+1) \rfloor \rfloor$, read as $0$ when $i \ge n$; for $i < n$ it is the length of the longest downward path from $i$ to a leaf, as [its recursion](heap-height-eq.md) shows.

**Theorem.** Let $a$ be an array of length $n$ over a linearly ordered type, let $b$ be the array returned by timed bottom-up heap construction on $a$, and let $S = \sum_{i=0}^{n-1} \lfloor \log_2 \lfloor n/(i+1) \rfloor \rfloor$ be the sum of the heights of the nodes of the level-order binary tree with $n$ nodes. Then:

1. $b$ is [heap ordered](heap-ordered.md), that is, every entry other than the root is at least the entry at its parent index, and $b$ is a permutation of $a$;
2. the construction counts at most $S$ array swaps and at most $2S$ value comparisons;
3. $S = n - s_2(n)$, where $s_2(n)$ is the sum of the binary digits of $n$;
4. if $n = 2^{h+1} - 1$ for a natural number $h$, so that the tree is perfect of height $h$, then $S = 2^{h+1} - 1 - (h + 1)$.

**Proof.**

1. While the positions $k - 1, \dots, 1, 0$ remain to be sifted down, every edge whose parent index is at least $k$ is ordered; at the start, $k = \lfloor n/2 \rfloor$ and no edge has a parent index that large. During the sift-down from $k$, let $i$ be the current position of the moving entry: every edge with parent index at least $k$ is ordered except those leaving $i$, and once the moving entry has moved below $k$ (that is, $i > k$), the entry above $i$ is at most both children of $i$. So when the sift-down stops, every edge with parent index at least $k$ is ordered. At $k = 0$ the whole array is heap ordered. Every step swaps two entries, so $b$ is a permutation of $a$.
2. Each node that a sift-down visits and that has a child costs at most two comparisons: one to choose the smaller child, made only when both children exist, and one against that child. A swap moves the entry to a child, whose height is at least one less, so these nodes have strictly decreasing heights, all at least $1$. Hence the sift-down from $i$ visits at most $\mathrm{height}(i)$ of them, so it makes at most $2\,\mathrm{height}(i)$ [comparisons](sift-down-comparisons-le-heap-height.md); it swaps at most once at each of them, so it makes at most $\mathrm{height}(i)$ [swaps](sift-down-swaps-le-heap-height.md). Summing over the internal positions, and adding the leaves, which have height $0$, gives at most $S$ swaps and $2S$ comparisons.
3. Write $S(n)$ for the sum. For $i < \lfloor n/2 \rfloor$ we have $\lfloor n/(i+1) \rfloor \ge 2$ and $\lfloor \lfloor n/(i+1) \rfloor / 2 \rfloor = \lfloor \lfloor n/2 \rfloor/(i+1) \rfloor$, so the height of $i$ in the tree with $n$ nodes is one more than in the tree with $\lfloor n/2 \rfloor$ nodes; every $i \ge \lfloor n/2 \rfloor$ is a leaf. Hence $S(n) = \lfloor n/2 \rfloor + S(\lfloor n/2 \rfloor)$, and since $s_2(n) = (n \bmod 2) + s_2(\lfloor n/2 \rfloor)$, induction on $n$ gives $S(n) + s_2(n) = n$. In particular $S \le n$, so the construction makes at most $n$ swaps and at most $2n$ comparisons.
4. The binary expansion of $2^{h+1} - 1$ consists of $h + 1$ ones, so part 3 gives $S = 2^{h+1} - 1 - (h + 1)$. Directly, as in the source: write $S = \sum_{i=0}^{h} 2^i (h - i)$ and compute $2S - S$. The terms involving $h$ cancel, leaving $S = -h + \sum_{j=1}^{h} 2^j = 2^{h+1} - 2 - h$.

[Heapsort with bottom-up heap construction](../../../sorting-and-searching/heapsort/bottom-up-heap-sort-correct-comparisons.md) builds on this construction.

## Background

- [Total sift-down cost is at most three per remaining level](sift-down-time-le.md)
- [Heap sort](../../../sorting-and-searching/heapsort/heap-sort.md)

## Sources

- R. W. Floyd, *Algorithm 245: Treesort 3*, Communications of the ACM 7(12), 701 (1964), doi:10.1145/355588.365103: the procedure first sifts down (its `siftup`) the positions $\lfloor n/2 \rfloor, \dots, 2$ of the array $M[1:n]$, indexed from $1$ and ordered as a max-heap, and sifts down the root at the start of its sorting loop. The construction here is that pass for a min-heap indexed from $0$, with the root included.
- C. Zander, *Linear heap algorithm (buildheap)*, course notes, CSS 343, University of Washington Bothell, <https://courses.washington.edu/css343/zander/NotesProbs/heapcomplexity>: bottom-up construction does work bounded by the sum of node heights, and the theorem that a complete binary tree of height $h$ with $2^{h+1} - 1$ nodes has height sum $2^{h+1} - 1 - (h + 1)$, proved by subtracting $S$ from $2S$. The bounds for general $n$, with the identity $S = n - s_2(n)$, are written out here.
