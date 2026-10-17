---
article_id: af_29df49191adef9258e6e5011
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.valid_delete
---

# Valid delete

Deletion always produces a valid red-black tree, with no hypothesis on
the input: the result is rebuilt by `fromList`, which is unconditionally
valid.

## Depends on

- [Tree](../../../part-03/red-black-tree/part-01/tree.md)
- [Valid](../../../part-03/red-black-tree/part-01/valid.md)
- [Delete](delete.md)

## Proof depends on

- [Del](del.md)
- [Inorder](../../../part-03/red-black-tree/part-01/inorder.md)
- [Rebalance](rebalance.md)
- [Valid from List](../../../part-03/red-black-tree/part-02/valid-from-list.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
