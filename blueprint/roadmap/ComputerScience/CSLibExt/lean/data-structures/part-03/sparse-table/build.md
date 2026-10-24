---
article_id: af_79a0e5dbaae9beee99de9da7
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.SparseTable.build
---

# Build

Builds the sparse table over `a` with `Nat.log2 a.length + 1` levels. Levels are
built iteratively: a fold threads one retained row through `buildStep`, computing each
level once from its predecessor, and stores the levels in an array. The input array is
bound once (`data`) and shared between level zero and the `data` field.

## Depends on

- [Sparse Table](sparse-table.md)

## Proof depends on

- [Build Step](build-step.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SparseTable](../../../../../../../sources/v2/CSLibExt.md)
