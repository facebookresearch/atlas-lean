# Rounding error is at most half a unit in the last place

Rounding to `k ≥ 1` significant figures changes `x` by at most half a unit in the last reported
place: the rounded value `r` satisfies `|r - x| ≤ (1 / 2) * 10 ^ (-e)`, where
`e = k - 1 - ⌊log₁₀ |x|⌋` is the [decimal shift](sig-fig-shift.md).
