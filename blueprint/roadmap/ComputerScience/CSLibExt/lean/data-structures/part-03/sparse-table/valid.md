---
article_id: af_a586cb2921db24de335860ef
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.SparseTable.Valid
---

# Valid

The representation invariant: every stored level is exactly `level data.toList`,
so a valid table's entries are the interval minima of its own data. Tables built by
`build` are valid (`build_valid`); an arbitrary value such as `⟨#[1], #[#[99]]⟩` is
not, and query correctness below is stated only for valid tables.

## Depends on

- [Sparse Table](sparse-table.md)

## Proof depends on

- [Level](level.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SparseTable](../../../../../../../sources/v2/CSLibExt.md)
