# Squared accuracy of the marginal PRS without LD

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with
`N ≠ 0` individuals and `M ≠ 0` markers, let `X` be a real `N × M` genotype matrix with
[orthogonal standardized columns](has-orthogonal-columns.md), so that its
[in-sample LD matrix](ld-matrix.md) is `R = I`, and let `β̂` be the
[normalized marginal scores](../ld-score-regression/beta-hat.md). With target LD matrix `R`, the
[squared accuracy](accuracy-sq-2.md) of the score `xᵀ β̂` is

`N h² / (N h² + M (1 - h²))`.
