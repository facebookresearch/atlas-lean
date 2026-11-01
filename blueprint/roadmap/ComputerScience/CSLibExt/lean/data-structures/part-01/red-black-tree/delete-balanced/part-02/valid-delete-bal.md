---
article_id: af_90e68629f9c2d4dcc93a25e3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.DeleteBalanced.valid_deleteBal
---

# Valid delete Bal

Deletion from a valid red-black tree leaves a valid tree. Only the
three structural invariants of `Valid` are used; see
`valid_deleteBal_of_invariants`.

## Depends on

- [Delete Bal](../part-01/delete-bal.md)
- [Tree](../../../../part-03/red-black-tree/part-01/tree.md)
- [Valid](../../../../part-03/red-black-tree/part-01/valid.md)

## Proof depends on

- [Balanced](../../../../part-03/red-black-tree/part-01/balanced.md)
- [Color](../../../../part-03/red-black-tree/part-01/color.md)
- [Valid delete Bal of invariants](valid-delete-bal-of-invariants.md)
- [Ordered](../../../../part-03/red-black-tree/part-01/ordered.md)
- [Red Ok](../../../../part-03/red-black-tree/part-01/red-ok.md)
- [Color Of](../../../../part-03/red-black-tree/part-01/color-of.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
