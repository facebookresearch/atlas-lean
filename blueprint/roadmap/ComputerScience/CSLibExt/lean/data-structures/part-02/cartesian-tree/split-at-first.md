---
article_id: af_d06d85292c22e591ea19df9a
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.CartesianTree.splitAtFirst
---

# Split At First

Split a list at the first occurrence of `m`, dropping that occurrence.
Only equality on `α` is needed, so this helper and its specification are
generalized over `[DecidableEq α]` rather than the `[LinearOrder α]`
required to build Cartesian trees.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.CartesianTree](../../../../../../../sources/v2/CSLibExt.md)
