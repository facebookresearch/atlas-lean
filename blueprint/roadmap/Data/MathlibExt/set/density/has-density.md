---
article_id: af_c95107daab57a358d9777e3e
declaration: def
origin: cited
statement: formalized
lean: Set.HasDensity
---

# Has Density

A set `S` in an order `β` where all intervals bounded above are finite is said to have
density `α : ℝ` (relative to a set `A`) if the proportion of `x ∈ S` such that `x < n`
in `A` tends to `α` as `n → ∞`.

When `β = ℕ` this by default defines the natural density of a set
(i.e., relative to all of `ℕ`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Partial Density](partial-density.md)

## Sources

- [MathlibExt, MathlibExt.Data.Set.Density](../../../../../sources/v2/MathlibExt.md)
