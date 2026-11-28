# Multilocus additive genetic variance

Let $L$ be a finite set of loci, $A_l$ a finite set of alleles at locus $l$,
$p_l : A_l \to \mathbb{R}$ real allele weights and $G_l(i, j)$ real genotypic values of the ordered
one-locus genotypes $(i, j)$. The multilocus additive genetic variance is the weighted sum of
squares of the [breeding value](breeding-value.md) $B$:

$$V_A = \sum_g f(g)\, B(g)^2,$$

summed over all ordered multilocus genotypes $g$ with their [weight](geno-freq.md)
$f(g) = \prod_l p_l(i_l)\, p_l(j_l)$. When every $p_l$ is a probability vector, the breeding value
has mean $0$ under these weights, since the [average effects](sum-mul-avg-effect.md) at each locus
have mean $0$, so $V_A$ is the variance of the breeding value.
