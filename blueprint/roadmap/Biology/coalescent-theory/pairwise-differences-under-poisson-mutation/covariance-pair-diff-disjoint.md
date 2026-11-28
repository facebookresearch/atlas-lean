# Covariance of the pairwise differences of two disjoint pairs

Let `θ ≥ 0` and let `a`, `b`, `c`, `d` be four distinct genes of a sample of size `n`. In the
[marked Kingman model](kingman-tree-mutation-measure.md) with mutation parameter `θ` (the
Kingman genealogy with a random-joining history, then, given the genealogy, independent Poisson
numbers of mutations on the branches, of mean `(θ/2) ℓ` on a branch of length `ℓ`), let `D_{ab}`
and `D_{cd}` be the [numbers of mutations](pair-diff.md) on the branches that separate `a` from
`b` and `c` from `d`, their numbers of pairwise differences under infinite sites. Then
(Tajima 1983)

`Cov(D_{ab}, D_{cd}) = θ/3 + 2θ²/9`.

This is the [general formula](covariance-pair-diff-kingman-tree-mutati.md)
`θ² Cov(τ_{ab}, τ_{cd}) + (θ/2) E[ℓ(P_{ab} ∩ P_{cd})]` with the
[covariance](covariance-pair-coal-time-disjoint.md) `2/9` of the coalescence times and the
[mean overlap](integral-pair-path-overlap-disjoint.md) `2/3` of the two paths.
