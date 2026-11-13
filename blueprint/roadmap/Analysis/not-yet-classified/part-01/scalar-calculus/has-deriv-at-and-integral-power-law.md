# Power laws

For every real exponent `r`, the power law `x ↦ x ^ r` (Mathlib's real
power `Real.rpow`) has derivative `r * x ^ (r - 1)` at each `0 < x`. If `-1 < r`, it is
interval integrable on `[0, 1]` and `∫ x in 0..1, x ^ r = 1 / (r + 1)`. The hypothesis
`-1 < r`, rather than `r ≠ -1`, is necessary: for `r < -1` the integrand is not integrable near
`0`, and the interval integral is Lean's junk value `0`.
