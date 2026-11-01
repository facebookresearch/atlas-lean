---
article_id: af_ac5a6102f1cd3fc7f35607f4
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.delete
---

# Delete

Delete a key from a B-tree of minimum degree `t` by a single top-down
pass, collapsing the root when a root merge leaves it keyless with a
single child. See the module documentation for the algorithm and its
specifications.

## Depends on

- [BTree](../../../btree-2/part-01/btree.md)

## Proof depends on

- [Del H](del-h.md)
- [Tree Height](tree-height.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
