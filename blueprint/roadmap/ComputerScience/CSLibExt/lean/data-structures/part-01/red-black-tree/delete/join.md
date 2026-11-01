---
article_id: af_0ba8025f2ac58e2fe8634c7c
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.join
---

# Join

Splice two trees end to end, keeping every key of the first tree before every
key of the second in the inorder traversal and keeping the existing colors.
`ordered_join` gives the side condition under which the splice of two ordered
trees stays ordered.

## Depends on

- [Tree](../../../part-03/red-black-tree/part-01/tree.md)

## Proof depends on

- [Color](../../../part-03/red-black-tree/part-01/color.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
