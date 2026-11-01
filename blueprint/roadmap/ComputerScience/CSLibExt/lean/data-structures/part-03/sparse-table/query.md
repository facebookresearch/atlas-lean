---
article_id: af_ef2c669e1cae15bac2ca8052
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.SparseTable.query
---

# Query

Range-minimum query over `[l, r)`: the minimum of the two length-`2 ^ k` entries starting
at `l` and at `r - 2 ^ k`, where `k = Nat.log2 (r - l)`. Empty intervals give `none`.

## Depends on

- [Sparse Table](sparse-table.md)

## Proof depends on

- [Entry](entry.md)
- [Omin](omin.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SparseTable](../../../../../../../sources/v2/CSLibExt.md)
