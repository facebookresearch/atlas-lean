---
article_id: af_c22834e2eea302d8bd1b2f09
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FenwickTree.Valid
---

# Valid

The tree represents `arr`: the stored array has one dummy entry plus one
entry per underlying element, and every stored entry equals its interval sum.
The underlying array itself is not stored at runtime; it appears only in this
specification relation.

## Depends on

- [Fenwick Tree](fenwick-tree.md)

## Proof depends on

- [Block Sum](block-sum.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FenwickTree](../../../../../../../../sources/v2/CSLibExt.md)
