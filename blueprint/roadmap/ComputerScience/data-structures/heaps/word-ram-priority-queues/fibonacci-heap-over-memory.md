# Fibonacci heap as an amortized refinement over memory

A Fibonacci heap on $n$ handles stored as a record of $O(n)$ named memory cells implements the indexed min-priority queue as an amortized refinement over word memory, with potential proportional to (number of roots $+ 2 \cdot$ number of marked nodes): insertion, decrease-key, minimum and membership have amortized cost $O(1)$ memory operations, and extract-min on a queue holding $m$ handles has amortized cost $O(\log m)$. The heap reads and writes only its own cells, so it can share one memory with other framed structures; zeroed memory is an empty heap.

## Proof sketch

Each heap operation is a fixed number of record-field reads and writes per step of its control flow; the potential pays for the cascading cuts of decrease-key and for the links of consolidation, as in Fredman and Tarjan's analysis, and potentials compose through the record layer.

## Depends on

- [Fibonacci heap](../fibonacci-heap/fibonacci-heap.md)
- [Indexed minimum queue](../indexed-minimum-priority-queue/indexed-min-queue.md)
- [Footprints and framing of data structures sharing one memory](../../data-structure-interfaces-and-refinement/footprints-and-framing.md)
- [Word-addressed memory as a specification](../../data-structure-interfaces-and-refinement/word-addressed-memory-specification.md)

## Proof depends on

- [Rank bound and amortized costs of Fibonacci heaps](../fibonacci-heap/rank-bound-and-amortized-costs-of-fibonacci-heaps.md)
- [Composition of amortized refinements adds potentials](../../data-structure-interfaces-and-refinement/composition-of-amortized-refinements.md)

## Sources

- M. L. Fredman and R. E. Tarjan, "Fibonacci Heaps and Their Uses in Improved Network Optimization Algorithms", Journal of the ACM 34(3), pp. 596-615, 1987.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
