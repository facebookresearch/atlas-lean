# Indexed binary heap on the Word RAM

The indexed binary min-heap over memory compiles to a fixed word-RAM register program that implements the indexed min-priority queue on $n$ handles with keys bounded by a word: insertion, decrease-key and extract-min run in $O(\log n)$ instructions each, membership and minimum queries in $O(1)$, and initialization in $O(n)$ instructions (or $O(1)$ on zeroed memory), with the heap occupying $O(n)$ words.

## Proof sketch

Each memory operation of the heap's methods is simulated by a constant number of word-RAM instructions, and the sift procedures perform $O(\log n)$ memory operations.

## Depends on

- [Indexed minimum queue](../indexed-minimum-priority-queue/indexed-min-queue.md)
- [Binary min-heap](../binary-heap/min-heap.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)

## Proof depends on

- [Memory-operation costs of an indexed binary heap](memory-costs-of-an-indexed-binary-heap.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
