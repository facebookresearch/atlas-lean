# For normalized weights the full-sib covariance sums over loci

Let $L$ be a finite set of loci and $A_l$ a finite set of alleles at locus $l$, and let the real
allele weights $p_l$ satisfy $\sum_{a \in A_l} p_l(a) = 1$ at every locus $l$; no sign condition is
needed. Then for all real genotypic values $G_l$ the
[multilocus full-sib covariance](cov-full-sibs-multi.md) $C_{FS}$ is the sum of the one-locus
[full-sib covariances](cov-full-sibs.md) $C_{FS,l}$ of $p_l$ and $G_l$:

$$C_{FS} = \sum_{l \in L} C_{FS,l}.$$
