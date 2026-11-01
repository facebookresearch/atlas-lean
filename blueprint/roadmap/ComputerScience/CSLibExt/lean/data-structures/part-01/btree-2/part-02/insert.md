---
article_id: af_a51dea02222fffb5ea70e5b0
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.insert
---

# Insert

Insert a key into a B-tree of minimum degree `t`, growing a new root with a single
separator exactly when the old root splits. Inserting an already-present key returns a
tree with the same flattening.

## Depends on

- [BTree](../part-01/btree.md)

## Proof depends on

- [Ins Result](../part-01/ins-result.md)
- [Ins](ins.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
