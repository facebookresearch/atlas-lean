# Marginal PRS calibration slope when target and training LD agree

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with `N`
individuals and `M` markers, let `X` be any real `N × M` genotype matrix with
[in-sample LD matrix](ld-matrix.md) `R`, and let `β̂` be the
[normalized marginal scores](../ld-score-regression/beta-hat.md). If the target LD matrix equals
`R`, the [calibration slope](calib-slope.md) of the score `xᵀ β̂` is

`(h² L / M) / (h² T / M + (1 - h²) L / N)`,

the [calibration-slope formula](slope-formula.md), where `L` is the
[sum of the LD scores](ld-score-sum.md) and `T` the
[trace of the cube of the LD matrix](ld-cube.md), with the convention `x / 0 = 0` on both sides:
both are `0` when the denominator vanishes, in particular when `N = 0` or `M = 0`. The slope need
not be `1`.
