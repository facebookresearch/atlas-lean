# Marginal PRS squared accuracy when target and training LD agree

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with
`N ≠ 0` individuals and `M ≠ 0` markers, let `X` be a
[standardized](../ld-score-regression/is-standardized.md) real `N × M` genotype matrix with
[in-sample LD matrix](ld-matrix.md) `R`, and let `β̂` be the
[normalized marginal scores](../ld-score-regression/beta-hat.md). If the target LD matrix equals the
training LD matrix `R`, the [squared accuracy](accuracy-sq-2.md) of the score `xᵀ β̂` for the
genetic value `xᵀ β` is

`(h² L / M)² / (h² (h² T / M + (1 - h²) L / N))`,

the [accuracy formula](accuracy-formula.md), where `L = tr R²` is the
[sum of the LD scores](ld-score-sum.md) and `T = tr R³` the
[trace of the cube of the LD matrix](ld-cube.md), with the convention `x / 0 = 0` (both sides are
`0` when `h² = 0`).
