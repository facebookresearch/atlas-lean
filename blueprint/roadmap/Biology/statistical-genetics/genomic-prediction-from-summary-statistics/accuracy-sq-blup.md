# Squared accuracy of the shrunk PRS

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with `N`
individuals and `M` markers, and let `X` be a real `N × M` genotype matrix whose
[second-moment matrix of the marginal scores](score-cov.md) `V` is invertible (`det V ≠ 0`). Let
`β̃` be the [shrunk estimates](blup-score.md) and let `S` be a real `M × M` matrix (target LD
matrix) with `C_S(β̃, β̃) ≠ 0`. Then the [squared accuracy](accuracy-sq-2.md) of the score `xᵀ β̃`
is

`C_S(β̃, β̃) / C_S(β, β)`,

with the convention `x / 0 = 0` (both sides are `0` when `C_S(β, β) = 0`). Here `C_S` is the
[training integral of the target cross moment](quad-cov.md).
