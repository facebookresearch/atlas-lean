---
article_id: af_baaf5ec4cc6bf4b966a98d87
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.DeleteBalanced.deleteBal
---

# Delete Bal

Delete a key by the double-black method. The result is again valid
when the input satisfies the three structural invariants `Ordered`,
`RedOk`, and `Balanced` (`valid_deleteBal_of_invariants`); in
particular `valid_deleteBal` covers `Valid tree`. The traversal
specifications `inorder_deleteBal` and `mem_deleteBal` require only
`Ordered tree`.

## Depends on

- [Tree](../../../../part-03/red-black-tree/part-01/tree.md)

## Proof depends on

- [Blacken](blacken.md)
- [Del](del.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
