---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MinHeap.extractMin_cons_elements
---

# Extract Min cons elements

A successful extraction partitions the original multiset into its result
and the returned heap, without using multiset erasure.

## Depends on

- [Min Heap](../part-02/min-heap.md)
- [Elements](../part-02/elements.md)
- [Extract Min](../part-02/extract-min.md)

## Proof depends on

- [Heap Ordered](../part-01/heap-ordered.md)
- [Empty](../part-02/empty.md)
- [Extract Tail](../part-02/extract-tail.md)
- [Move Last To Root](../part-02/move-last-to-root.md)
- [Move Last To Root sift Down Ready](../part-02/move-last-to-root-sift-down-ready.md)
- [Sift Down](../part-01/sift-down.md)
- [Sift Down ordered](../part-01/sift-down-ordered.md)
- [Sift Down perm](../part-01/sift-down-perm.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap](../../../../../../../../sources/v2/CSLibExt.md)
