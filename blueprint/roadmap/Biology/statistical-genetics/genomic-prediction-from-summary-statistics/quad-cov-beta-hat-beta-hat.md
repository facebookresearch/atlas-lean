# Score term of the marginal PRS when target and training LD agree

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with `N`
individuals and `M` markers, and let `X` be a real `N × M` genotype matrix with
[in-sample LD matrix](ld-matrix.md) `R`. Let `β̂` be the
[normalized marginal scores](../ld-score-regression/beta-hat.md). With target LD matrix `S = R`, the
[training integral of the target cross moment](quad-cov.md) of the scores with themselves is

`C_R(β̂, β̂) = (h² / M) T + ((1 - h²) / N) L`,

where `L` is the [sum of the LD scores](ld-score-sum.md) and `T` the
[trace of the cube of the LD matrix](ld-cube.md), with the convention `x / 0 = 0` (both sides are
`0` when `N = 0` or `M = 0`).
