# Decimal shift for k significant figures

The decimal shift `k - 1 - ⌊log₁₀ |x|⌋` that moves the `k`-th significant digit of `x` to the units
place, for a count `k ≥ 1` (`k = 0` has no significant-figure interpretation). With the convention
`log₁₀ 0 = 0` it is `k - 1` at `x = 0`.
