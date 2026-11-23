# The shrunk PRS is calibrated when its score term is nonzero

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with `N`
individuals and `M` markers, and let `X` be a real `N × M` genotype matrix whose
[second-moment matrix of the marginal scores](score-cov.md) `V` is invertible (`det V ≠ 0`). Let
`β̃ = (h² / M) R V⁻¹ β̂` be the [shrunk estimates](blup-score.md), where `R` is the
[in-sample LD matrix](ld-matrix.md) and `β̂` the
[normalized marginal scores](../ld-score-regression/beta-hat.md). Then for every real `M × M` matrix
`S` (target LD matrix) with `C_S(β̃, β̃) ≠ 0`, the [calibration slope](calib-slope.md) of the score
`xᵀ β̃` is exactly `1`. Here `C_S` is the
[training integral of the target cross moment](quad-cov.md).
