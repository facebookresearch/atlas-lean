---
article_id: af_7385ca565cc567c53e48b343
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TimeM.siftDown
---

# Sift Down

Sift-down with `(value comparisons, array swaps)` as its event cost.
Index arithmetic, bounds checks, pattern matching and recursive calls are free.
The child-selection comparison is charged only when both children exist.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ret timed Smaller Child](ret-timed-smaller-child.md)
- [Timed Smaller Child](timed-smaller-child.md)
- [Smaller Child](../../../part-02/binary-heap/part-01/smaller-child.md)
- [Smaller Child gt](../../../part-02/binary-heap/part-01/smaller-child-gt.md)
- [Smaller Child valid](../../../part-02/binary-heap/part-01/smaller-child-valid.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.SiftDownCost](../../../../../../../../sources/v2/CSLibExt.md)
