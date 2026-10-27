---
article_id: af_903e6e720cbebc86a4d70b00
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.valid_insert_of_invariants
---

# Valid insert of invariants

Insertion yields a valid tree from the three structural invariants
`Ordered`, `RedOk`, and `Balanced`; the input root need not be black,
since `insert` recolors the root black.

## Depends on

- [Balanced](../part-01/balanced.md)
- [Ordered](../part-01/ordered.md)
- [Red Ok](../part-01/red-ok.md)
- [Tree](../part-01/tree.md)
- [Valid](../part-01/valid.md)
- [Insert](insert.md)

## Proof depends on

- [Color](../part-01/color.md)
- [Balanced insert](balanced-insert.md)
- [Color Of](../part-01/color-of.md)
- [Ins](ins.md)
- [Make Black](make-black.md)
- [Ordered insert](ordered-insert.md)
- [Red Ok insert](red-ok-insert.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree](../../../../../../../../sources/v2/CSLibExt.md)
