# Covariance of the pairwise differences of two pairs sharing a gene

Let `θ ≥ 0` and let `a`, `b`, `c` be three distinct genes of a sample of size `n`. In the
[marked Kingman model](kingman-tree-mutation-measure.md) with mutation parameter `θ` (the
Kingman genealogy with a random-joining history, then, given the genealogy, independent Poisson
numbers of mutations on the branches, of mean `(θ/2) ℓ` on a branch of length `ℓ`), let `D_{ab}`
and `D_{ac}` be the [numbers of mutations](pair-diff.md) on the branches that separate `a` from
`b` and `a` from `c`, their numbers of pairwise differences under infinite sites. Then
(Tajima 1983)

`Cov(D_{ab}, D_{ac}) = θ/2 + θ²/3`.

This is the [general formula](covariance-pair-diff-kingman-tree-mutati.md)
`θ² Cov(τ_{ab}, τ_{ac}) + (θ/2) E[ℓ(P_{ab} ∩ P_{ac})]` with the
[covariance](covariance-pair-coal-time-shared.md) `1/3` of the coalescence times and the
[mean overlap](integral-pair-path-overlap-shared.md) `1` of the two paths.
