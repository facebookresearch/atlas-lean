---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.siftDown_ordered
---

# Sift Down ordered

Sifting down an array with admissible outgoing-edge violations restores
the local heap-order invariant. This theorem is reusable independently of
`MinHeap`, for example by heap-sort developments.

## Depends on

- [Heap Ordered](heap-ordered.md)
- [Sift Down Ready](sift-down-ready.md)
- [Sift Down](sift-down.md)

## Proof depends on

- [Heap Left](heap-left.md)
- [Heap Parent](heap-parent.md)
- [Heap Parent lt size](heap-parent-lt-size.md)
- [Heap Right](heap-right.md)
- [Smaller Child](smaller-child.md)
- [Smaller Child gt](smaller-child-gt.md)
- [Smaller Child valid](smaller-child-valid.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap](../../../../../../../../sources/v2/CSLibExt.md)
