# Cross moments of effects and marginal scores under LD

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with `N`
individuals and `M` markers, and let `X` be a real `N × M` genotype matrix with
[in-sample LD matrix](ld-matrix.md) `R`. Then for all markers `k, l` the effect `β_k` and the
[normalized marginal score](../ld-score-regression/beta-hat.md) `β̂_l` satisfy

`∫ β_k β̂_l dμ = (h² / M) R_lk`.
