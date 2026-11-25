# Squared-accuracy formula in terms of LD moments

For natural numbers `N`, `M` and real numbers `h²`, `L`, `T`, the accuracy formula is

`(h² L / M)² / (h² (h² T / M + (1 - h²) L / N))`,

with the convention `x / 0 = 0` throughout: `h² L / M` and `h² T / M` are `0` when `M = 0`,
`(1 - h²) L / N` is `0` when `N = 0`, and the value is `0` when the denominator vanishes (for
example when `h² = 0`). It is meant for `N, M ≥ 1` and a nonzero denominator; with `L` the
[sum of the LD scores](ld-score-sum.md) and `T` the [trace of the cube of the LD matrix](ld-cube.md)
it is the [squared accuracy of the marginal PRS](accuracy-sq-marginal.md) for a standardized
genotype matrix.
