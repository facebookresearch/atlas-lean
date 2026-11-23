# Product moment of two pairwise differences in the marked Kingman model

Let `n ≥ 2`, `θ ≥ 0`, and let `s` and `s'` be
[pairs](../segregating-sites-and-pairwise-differences/sample-pairs.md) of genes of a sample of
size `n`. Under the [marked Kingman model](kingman-tree-mutation-measure.md) the
[numbers of differences](pair-diff.md) `D_s` and `D_{s'}` satisfy

`E[D_s D_{s'}] = θ² E_G[τ_s τ_{s'}] + (θ / 2) E_G[ℓ(P(s) ∩ P(s'))]`,

where `E_G` is the expectation under the [Kingman genealogy law](kingman-genealogy-measure.md),
`τ_s` is the [coalescence time](pair-coal-time.md) of `s` and `ℓ(P(s) ∩ P(s'))` is the
[overlap length](pair-path-overlap.md) of the paths separating the two pairs. The first term is
the mean of the product of the conditional means `θ τ_s` and `θ τ_{s'}`; the second is the
Poisson variance of the mutations on the branches separating both pairs. The identity expresses
these second moments, which enter Tajima's `Var π`, through moments of the genealogy.
