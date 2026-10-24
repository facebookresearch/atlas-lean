---
article_id: af_d20b48ea36db083551b6523d
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.DaryMinHeap.extractMin
---

# Extract Min

Remove and return the minimum. The last entry moves to the root and
sifts down, so extraction follows one `d`-ary child path.

## Depends on

- [Dary Min Heap](../part-02/dary-min-heap.md)

## Proof depends on

- [Extract Tail](extract-tail.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.DaryHeap](../../../../../../../../sources/v2/CSLibExt.md)
