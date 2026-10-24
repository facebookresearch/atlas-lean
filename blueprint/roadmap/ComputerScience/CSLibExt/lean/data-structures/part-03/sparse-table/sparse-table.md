---
article_id: af_9ab276de1118a4cc168b49cb
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.SparseTable
---

# Sparse Table

A sparse table over `α`: the underlying data together with its levels of interval
minima, stored as arrays so that entry lookup is random access. The list-level function
`level`, together with `List.min?` of slices of `data.toList`, is the specification.
Arbitrary values of this type need not relate `data` and `levels` at all; the
representation invariant `Valid` ties every stored level to `level data.toList`,
`build` produces valid tables, and query correctness is stated for valid tables.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SparseTable](../../../../../../../sources/v2/CSLibExt.md)
