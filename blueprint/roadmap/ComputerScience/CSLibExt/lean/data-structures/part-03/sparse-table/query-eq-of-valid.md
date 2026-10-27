---
article_id: af_614e7c4ed8f3ad07d0773a8e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.SparseTable.query_eq_of_valid
---

# Query eq of valid

A query on a valid table is `List.min?` of the corresponding list slice.
Only the in-range premise `r ≤ t.data.toList.length` is needed: for reversed
bounds `r ≤ l` both sides are `none`.

## Depends on

- [Sparse Table](sparse-table.md)
- [Valid](valid.md)
- [Query](query.md)

## Proof depends on

- [Entry](entry.md)
- [Entry eq of valid](entry-eq-of-valid.md)
- [Level](level.md)
- [Omin](omin.md)
- [Omin self](omin-self.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SparseTable](../../../../../../../sources/v2/CSLibExt.md)
