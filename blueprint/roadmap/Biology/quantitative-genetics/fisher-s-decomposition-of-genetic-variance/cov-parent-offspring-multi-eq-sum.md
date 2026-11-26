# For normalized weights the parent–offspring covariance sums over loci

Let $L$ be a finite set of loci and $A_l$ a finite set of alleles at locus $l$, and let the real
allele weights $p_l$ satisfy $\sum_{a \in A_l} p_l(a) = 1$ at every locus $l$; no sign condition is
needed. Then for all real genotypic values $G_l$ the
[multilocus parent–offspring covariance](cov-parent-offspring-multi.md) $C_{PO}$ is the sum of the
one-locus [parent–offspring covariances](cov-parent-offspring.md) $C_{PO,l}$ of $p_l$ and $G_l$:

$$C_{PO} = \sum_{l \in L} C_{PO,l}.$$
