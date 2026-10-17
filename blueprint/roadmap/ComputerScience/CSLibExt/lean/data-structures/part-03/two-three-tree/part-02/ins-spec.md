---
article_id: af_ddcd1aa3950dc45741f3cf0d
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TwoThreeTree.InsSpec
---

# Ins Spec

The specification of `ins x t` as an `Overflow` of a given source tree `t`:
in the `ok` case the result is ordered with the expected flattening, and in the
`split` case both parts are ordered, separated by the promoted key, with the
expected combined flattening.

## Depends on

- [Overflow](../part-01/overflow.md)
- [Tree](../part-01/tree.md)

## Proof depends on

- [All](../part-01/all.md)
- [Ordered](../part-01/ordered.md)
- [Flatten](../part-01/flatten.md)
- [Ordered Insert](../../../part-02/ordered-insert/ordered-insert.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.TwoThreeTree](../../../../../../../../sources/v2/CSLibExt.md)
