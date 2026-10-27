---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.siftUp_ordered
---

# Sift Up ordered

Sifting up an array with one admissible incoming-edge violation restores
the local heap-order invariant.

## Depends on

- [Heap Ordered](heap-ordered.md)
- [Sift Up Ready](sift-up-ready.md)
- [Sift Up](sift-up.md)

## Proof depends on

- [Heap Parent](heap-parent.md)
- [Heap Parent lt size](heap-parent-lt-size.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap](../../../../../../../../sources/v2/CSLibExt.md)
