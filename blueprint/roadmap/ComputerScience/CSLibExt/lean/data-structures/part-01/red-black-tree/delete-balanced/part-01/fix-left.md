---
article_id: af_a1f86f4ddc0454b1e26a35a0
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.DeleteBalanced.fixLeft
---

# Fix Left

Repair a black-height deficit in the left child. Here `left` is the
deficient subtree with its double black already absorbed, so
`blackHeight left + 1 = blackHeight right`; `color` and `key` are the parent
color and key. The cases, in order: a black sibling with a red far (right)
nephew (single rotation), a black sibling with a red near (left) nephew
(double rotation), a black sibling with two black nephews (redden the
sibling and bubble the double black into the parent), and a red sibling
(rotate it up and solve the black-sibling problem under the resulting red
parent; the three subcases mirror the black-sibling cases).

## Depends on

- [Color](../../../../part-03/red-black-tree/part-01/color.md)
- [BBTree](bbtree.md)
- [Tree](../../../../part-03/red-black-tree/part-01/tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
