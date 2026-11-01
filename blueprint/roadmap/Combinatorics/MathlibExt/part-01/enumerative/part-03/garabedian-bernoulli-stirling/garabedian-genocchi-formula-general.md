---
article_id: af_12ae8a912db22c91e10d8cb3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.garabedian_genocchi_formula_general
---

# Garabedian genocchi formula general

Garabedian's Bernoulli-number identity in Stirling form for every `n : ℕ`:
`2 * (1 - 2 ^ n) * B n` equals `n` times the signed sum of
`(-1) ^ (n - k) * (k - 1)! * S(n, k) / 2 ^ (k - 1)` over `1 ≤ k ≤ n`,
with `B = bernoulli` and `S = Nat.stirlingSecond`. The cited source states the case
`n ≥ 1`; at `n = 0` both sides are `0`. `garabedian_genocchi_formula` is the
source-shaped form.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.GarabedianBernoulliStirling](../../../../../../../sources/v2/MathlibExt.md)
