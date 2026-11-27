# Memory-operation costs of an indexed binary heap

An indexed binary min-heap over a word-addressed memory, with position and key arrays, implements the indexed min-priority queue on $n$ handles. Sift-up from position $k$ repairs one order defect within $O(1 + \log k)$ memory operations and sift-down within $O(1 + \log S - \log k)$ on a heap of size $S$, so every operation costs $O(1 + \log n)$ memory operations. The heap reads and writes only its own region, so it composes with other framed structures in one memory.

## Proof sketch

Each level of a sift compares a node with its parent or its smaller child and possibly swaps, with a constant number of reads and writes; the number of levels is the difference of the binary logarithms of the positions.

## Depends on

- [Binary min-heap](../binary-heap/min-heap.md)
- [Indexed minimum queue](../indexed-minimum-priority-queue/indexed-min-queue.md)
- [Footprints and framing of data structures sharing one memory](../../data-structure-interfaces-and-refinement/footprints-and-framing.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
