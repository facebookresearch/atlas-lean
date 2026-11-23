# Multilocus genetic variance

Let $L$ be a finite set of loci, $A_l$ a finite set of alleles at locus $l$,
$p_l : A_l \to \mathbb{R}$ real allele weights and $G_l(i, j)$ real genotypic values of the ordered
one-locus genotypes $(i, j)$. The multilocus genetic variance is

$$V_G = \sum_g f(g)\, \bigl(G(g) - \mu\bigr)^2,$$

the sum over all ordered multilocus genotypes $g$, with $g_l = (i_l, j_l)$, of their
[weight](geno-freq.md) $f(g) = \prod_l p_l(i_l)\, p_l(j_l)$ times the squared deviation of their
[genotypic value](total-value.md) $G(g) = \sum_l G_l(i_l, j_l)$ from the
[multilocus mean](multi-mean.md) $\mu$. When every $p_l$ is a probability vector, it is the variance
of the genotypic value under Hardy–Weinberg proportions at every locus and linkage equilibrium.
