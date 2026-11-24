# Twice the kinship matrix of an IBD model is positive semidefinite

Let `D` be an
[identity-by-descent model](../../../quantitative-genetics/genomic-relationship-matrices/ibdmodel.md)
on a finite set of individuals, for a probability measure `μ`, with reference-allele frequency
`0 < p < 1`. Then the matrix `2 φ` with entries `2 φᵢⱼ`, where `φ` is the
[kinship coefficient](../../../quantitative-genetics/genomic-relationship-matrices/kinship.md) of
`D`, is positive semidefinite. It is the covariance matrix of the
[genotypes](../../../quantitative-genetics/genomic-relationship-matrices/genotype.md) divided by
`2p(1 - p) > 0`: `Cov(xᵢ, xⱼ) = 2p(1 - p) · 2 φᵢⱼ`
([the genetic relationship covariance](../../../quantitative-genetics/genomic-relationship-matrices/integral-centered-mul.md)).
