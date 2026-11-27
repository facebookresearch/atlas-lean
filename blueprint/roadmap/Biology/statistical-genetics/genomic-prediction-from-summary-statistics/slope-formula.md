# Calibration-slope formula in terms of LD moments

For natural numbers `N`, `M` and real numbers `h²`, `L`, `T`, the calibration-slope formula is

`(h² L / M) / (h² T / M + (1 - h²) L / N)`,

with the convention `x / 0 = 0` throughout: `h² L / M` and `h² T / M` are `0` when `M = 0`,
`(1 - h²) L / N` is `0` when `N = 0`, and the value is `0` when the denominator vanishes. It is
meant for `N, M ≥ 1` and a nonzero denominator; with `L` the [sum of the LD scores](ld-score-sum.md)
and `T` the [trace of the cube of the LD matrix](ld-cube.md) it is the
[calibration slope of the marginal PRS](calib-slope-marginal.md).
