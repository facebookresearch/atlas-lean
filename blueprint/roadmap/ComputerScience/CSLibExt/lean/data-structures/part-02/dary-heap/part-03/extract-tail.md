---
article_id: af_046baab5a10f33b56c47f5d8
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.DaryMinHeap.extractTail
---

# Extract Tail

Remove the root from a known nonempty heap and restore heap order:
the last entry moves to the root and sifts down its `d`-ary child path.

## Depends on

- [Dary Min Heap](../part-02/dary-min-heap.md)

## Proof depends on

- [Dary Heap Ordered](../part-01/dary-heap-ordered.md)
- [Dary Move Last To Root](../part-02/dary-move-last-to-root.md)
- [Dary Move Last To Root sift Down Ready](../part-02/dary-move-last-to-root-sift-down-ready.md)
- [Dary Parent](../part-01/dary-parent.md)
- [Dary Parent lt size](../part-01/dary-parent-lt-size.md)
- [Dary Sift Down](../part-02/dary-sift-down.md)
- [Dary Sift Down ordered](../part-02/dary-sift-down-ordered.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.DaryHeap](../../../../../../../../sources/v2/CSLibExt.md)
