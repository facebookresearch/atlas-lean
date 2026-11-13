# Sample Var

The divide-by-`n` sample variance `(∑ i, (x i - x̄) ^ 2) / n` (MF06.3). Mathlib has no
sample variance of real data; Batteries' `RunningStats.sampleVariance` is a `Float` accumulator.
ATLAS's `MathlibExt.Probability.Causality` has no counterpart: its `popVar` and its
`Finset`-indexed `sampleVar` divide by `n - 1` and `|S| - 1`.
