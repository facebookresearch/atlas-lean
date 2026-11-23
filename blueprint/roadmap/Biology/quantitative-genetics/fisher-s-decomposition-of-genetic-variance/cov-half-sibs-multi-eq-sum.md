# For normalized weights the half-sib covariance sums over loci

Let $L$ be a finite set of loci and $A_l$ a finite set of alleles at locus $l$, and let the real
allele weights $p_l$ satisfy $\sum_{a \in A_l} p_l(a) = 1$ at every locus $l$; no sign condition is
needed. Then for all real genotypic values $G_l$ the
[multilocus half-sib covariance](cov-half-sibs-multi.md) $C_{HS}$ is the sum of the one-locus
[half-sib covariances](cov-half-sibs.md) $C_{HS,l}$ of $p_l$ and $G_l$:

$$C_{HS} = \sum_{l \in L} C_{HS,l}.$$
