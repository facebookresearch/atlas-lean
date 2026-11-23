# Squared accuracy without LD matches the derived effect-estimate model

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with
`N ≠ 0` individuals and `M ≠ 0` markers, let `X` be a real `N × M` genotype matrix with
[orthogonal standardized columns](has-orthogonal-columns.md) and [in-sample LD matrix](ld-matrix.md)
`R`, and let `β̂` be the [normalized marginal scores](../ld-score-regression/beta-hat.md). With
target LD matrix `R`, the [squared accuracy](accuracy-sq-2.md) of the score `xᵀ β̂` equals the
[squared accuracy](accuracy-sq.md) of the
[effect-estimate model derived from the LD-score model](of-ldscore.md). By
[polygenic-score accuracy in the LD-score model](accuracy-sq-of-ldscore.md), both are
`N h² / (N h² + M (1 - h²))`.
