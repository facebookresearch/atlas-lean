---
article_id: af_c8cad50277483840ddbe9708
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.del
---

# Del

Unbalanced deletion: delete a key by comparisons, splicing the subtrees of a
deleted node together with `join`. Colors are kept, but `RedOk` and
`Balanced` need not hold of the result; `delete` repairs them.

## Depends on

- [Tree](../../../part-03/red-black-tree/part-01/tree.md)

## Proof depends on

- [Color](../../../part-03/red-black-tree/part-01/color.md)
- [Join](join.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
