---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.push_siftUpReady
---

# Push sift Up Ready

Appending to an ordered heap creates exactly the admissible sift-up
violation at the new last index.

## Depends on

- [Heap Ordered](heap-ordered.md)
- [Sift Up Ready](sift-up-ready.md)

## Proof depends on

- [Heap Parent](heap-parent.md)
- [Heap Parent lt size](heap-parent-lt-size.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap](../../../../../../../../sources/v2/CSLibExt.md)
