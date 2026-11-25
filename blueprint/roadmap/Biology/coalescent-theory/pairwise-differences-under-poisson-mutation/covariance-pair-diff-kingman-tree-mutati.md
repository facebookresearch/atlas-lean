# Covariance of two pairwise differences in the marked Kingman model

Let `n ≥ 2`, `θ ≥ 0`, and let `s` and `s'` be
[pairs](../segregating-sites-and-pairwise-differences/sample-pairs.md) of genes of a sample of
size `n`. Under the [marked Kingman model](kingman-tree-mutation-measure.md) the
[numbers of differences](pair-diff.md) `D_s` and `D_{s'}` have covariance

`Cov(D_s, D_{s'}) = θ² Cov_G(τ_s, τ_{s'}) + (θ / 2) E_G[ℓ(P(s) ∩ P(s'))]`,

where `Cov_G` and `E_G` are the covariance and the expectation under the
[Kingman genealogy law](kingman-genealogy-measure.md), `τ_s` is the
[coalescence time](pair-coal-time.md) of `s` and `ℓ(P(s) ∩ P(s'))` is the
[overlap length](pair-path-overlap.md) of the paths separating the two pairs. Here `D_s`, `D_{s'}`,
`τ_s` and `τ_{s'}` are square integrable, so both covariances are finite.
