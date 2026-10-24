---
article_id: af_335868ea1eadec2418711edd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.DeleteBalanced.valid_deleteBal_of_invariants
---

# Valid delete Bal of invariants

Deletion yields a valid tree from the three structural invariants
`Ordered`, `RedOk`, and `Balanced`; the input root need not be black,
since `deleteBal` blackens the root.

## Depends on

- [Balanced](../../../../part-03/red-black-tree/part-01/balanced.md)
- [Delete Bal](../part-01/delete-bal.md)
- [Ordered](../../../../part-03/red-black-tree/part-01/ordered.md)
- [Red Ok](../../../../part-03/red-black-tree/part-01/red-ok.md)
- [Tree](../../../../part-03/red-black-tree/part-01/tree.md)
- [Valid](../../../../part-03/red-black-tree/part-01/valid.md)

## Proof depends on

- [All](../../../../part-02/binary-search-tree/part-01/all.md)
- [Ordered](../../../../part-02/binary-search-tree/part-01/ordered.md)
- [Inorder](../../../../part-02/binary-search-tree/part-01/inorder.md)
- [Inorder Aux](../../../../part-02/binary-search-tree/part-01/inorder-aux.md)
- [All](../../../../part-03/red-black-tree/part-01/all.md)
- [Color](../../../../part-03/red-black-tree/part-01/color.md)
- [BBTree](../part-01/bbtree.md)
- [BColor](../part-01/bcolor.md)
- [Balanced BB](../part-01/balanced-bb.md)
- [Red Ok BB](../part-01/red-ok-bb.md)
- [Bal Left](../part-01/bal-left.md)
- [Bal Right](../part-01/bal-right.md)
- [Bh BB](../part-01/bh-bb.md)
- [Blacken](../part-01/blacken.md)
- [Color BB](../part-01/color-bb.md)
- [Del](../part-01/del.md)
- [Fix Left](../part-01/fix-left.md)
- [Fix Right](../part-01/fix-right.md)
- [Incr Black](../part-01/incr-black.md)
- [Inorder BB](../part-01/inorder-bb.md)
- [Min Key](../part-01/min-key.md)
- [Ordered delete Bal](ordered-delete-bal.md)
- [Root Black](../part-01/root-black.md)
- [Mem](../../../../part-03/red-black-tree/part-01/mem.md)
- [All iff forall mem](../../../../part-03/red-black-tree/part-02/all-iff-forall-mem.md)
- [Black Height](../../../../part-03/red-black-tree/part-01/black-height.md)
- [Color Of](../../../../part-03/red-black-tree/part-01/color-of.md)
- [Erase](../../../../part-03/red-black-tree/part-01/erase.md)
- [Inorder](../../../../part-03/red-black-tree/part-01/inorder.md)
- [Mem inorder](../../../../part-03/red-black-tree/part-02/mem-inorder.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
