# Full-sib covariance over loci in terms of variance components

Let $L$ be a finite set of loci and $A_l$ a finite set of alleles at locus $l$, and let the real
allele weights $p_l$ satisfy $\sum_{a \in A_l} p_l(a) = 1$ at every locus $l$; no sign condition is
needed. Let the real genotypic values be symmetric, $G_l(i, j) = G_l(j, i)$. Then the
[multilocus full-sib covariance](cov-full-sibs-multi.md) is

$$C_{FS} = \frac{V_A}{2} + \frac{V_D}{4},$$

where $V_A$ and $V_D$ are the multilocus [additive](multi-add-var.md) and
[dominance](multi-dom-var.md) variances (Fisher 1918).
