# Marginal scores as LD-weighted effects plus noise

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with `N`
individuals and `M` markers, and let `X` be a real `N × M` genotype matrix with
[in-sample LD matrix](ld-matrix.md) `R`. Then the
[normalized marginal score](../ld-score-regression/beta-hat.md) of each marker `j` is, pointwise on
`Ω`,

`β̂_j = ∑_k R_jk β_k + ∑_i (X_ij / N) ε_i`:

the effects weighted by their LD with marker `j`, plus sampling noise. With the convention
`x / 0 = 0`, both sides are `0` when `N = 0`.
