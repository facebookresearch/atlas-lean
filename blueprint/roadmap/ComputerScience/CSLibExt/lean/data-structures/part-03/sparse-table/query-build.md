---
article_id: af_4e2d71d90eff41b4af4e6e98
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.SparseTable.query_build
---

# Query build

A query on a built table is `List.min?` of the corresponding list slice,
with no ordering premise on the bounds.

## Depends on

- [Build](build.md)
- [Query](query.md)

## Proof depends on

- [Sparse Table](sparse-table.md)
- [Build valid](build-valid.md)
- [Query eq of valid](query-eq-of-valid.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SparseTable](../../../../../../../sources/v2/CSLibExt.md)
