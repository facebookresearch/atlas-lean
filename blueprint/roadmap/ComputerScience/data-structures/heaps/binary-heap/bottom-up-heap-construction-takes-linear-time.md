# Bottom-up heap construction takes linear time

*Bottom-up heap construction* turns an arbitrary array $a$ of length $n$ into a [binary min-heap](min-heap.md). It [sifts down](sift-down.md) every internal position $i = \lfloor n/2 \rfloor - 1, \dots, 1, 0$ in turn, from the last internal node back to the root, using 0-indexed level-order storage. The *height* of position $i$ is the length of the longest downward path from $i$ to a leaf.

**Theorem.**
1. Bottom-up construction produces a heap, and it performs at most $\sum_i \mathrm{height}(i) = O(n)$ swaps and $O(n)$ comparisons.
2. For a perfect binary tree of height $h$, with $n = 2^{h+1} - 1$ nodes, the heights sum to exactly $2^{h+1} - 1 - (h + 1) = n - \log_2(n + 1)$.
3. Consequently, heapsort, which consists of bottom-up construction followed by $n$ extract-min operations, each sifting down from the root in $O(\log n)$ steps, sorts $n$ items with $O(n \log n)$ comparisons.

**Proof.**
1. After position $i$ is sifted down, the subtree rooted at $i$ is heap-ordered, because both child subtrees were heap-ordered beforehand. Induction downward over $i$ gives the heap property. A sift-down from a node of height $k$ makes at most $k$ swaps and $O(k)$ comparisons, and at most $\lceil n/2^{k+1} \rceil$ nodes have height $k$. Heights are at most $\lfloor \log_2 n \rfloor$, so the total is $\sum_{k=1}^{\lfloor \log_2 n \rfloor} k\lceil n/2^{k+1}\rceil \le n\sum_{k \ge 1} k/2^{k+1} + O(\log^2 n) = n + O(\log^2 n) = O(n)$.
2. Write $S = \sum_{i=0}^{h} 2^i (h - i)$ and compute $2S - S$. The terms involving $h$ cancel, leaving $S = -h + \sum_{j=1}^{h} 2^j = 2^{h+1} - 2 - h$.
3. This follows from part 1 and the logarithmic [cost of sift-down](sift-down-time-le.md).

## Depends on

- [Binary min-heap](min-heap.md)
- [Sift-down](sift-down.md)

## Background

- [Total sift-down cost is at most three per remaining level](sift-down-time-le.md)
- [Heap sort](../../../sorting-and-searching/heapsort/heap-sort.md)

## Sources

- C. Zander, *Linear heap algorithm (buildheap)*, course notes, CSS 343, University of Washington Bothell, <https://courses.washington.edu/css343/zander/NotesProbs/heapcomplexity>: bottom-up construction does work bounded by the sum of node heights, and the theorem that a complete binary tree of height $h$ with $2^{h+1} - 1$ nodes has height sum $2^{h+1} - 1 - (h + 1)$, proved by subtracting $S$ from $2S$. The bound for general $n$ and the heapsort corollary are written out here.
