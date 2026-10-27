---
article_id: af_d4396956e5d0805e7e9bb05c
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.deleteRebuild
---

# Delete Rebuild

Delete a key from a B-tree of minimum degree `t` by rebuilding:
erase the key from the inorder flattening and rebuild with `fromList`.
The primary deletion operation is `delete` in
`CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced`. See the
module documentation for the exact sense in which this is, and is not,
the CLRS 18.3 algorithm.

## Depends on

- [BTree](../../btree-2/part-01/btree.md)

## Proof depends on

- [Flatten](../../btree-2/part-01/flatten.md)
- [From List](../../btree-2/part-02/from-list.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
