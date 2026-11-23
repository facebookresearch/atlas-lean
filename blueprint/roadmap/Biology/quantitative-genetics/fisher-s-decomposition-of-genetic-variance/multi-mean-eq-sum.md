# For normalized weights the mean is a sum over loci

Let $L$ be a finite set of loci and $A_l$ a finite set of alleles at locus $l$, and let the real
allele weights $p_l$ satisfy $\sum_{a \in A_l} p_l(a) = 1$ at every locus $l$; no sign condition is
needed. Then for all real genotypic values $G_l$ the
[multilocus mean genotypic value](multi-mean.md) is the sum of the one-locus [means](mean-value.md):

$$\mu = \sum_{l \in L} \mu_l, \qquad \mu_l = \sum_{i, j \in A_l} p_l(i)\, p_l(j)\, G_l(i, j).$$
