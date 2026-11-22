# Decimal shift for k significant figures

The decimal shift `k - 1 - ⌊log₁₀ |x|⌋` that moves the `k`-th significant digit of `x` to the
units place. With Mathlib's convention `Real.logb 10 0 = 0` it is `k - 1` at `x = 0`. The count
`k : ℕ+` is positive by type: `k = 0` has no significant-figure interpretation and is excluded.
