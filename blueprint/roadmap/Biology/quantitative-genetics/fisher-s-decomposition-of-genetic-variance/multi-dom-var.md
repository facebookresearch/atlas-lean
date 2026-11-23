# Multilocus dominance variance

Let $L$ be a finite set of loci, $A_l$ a finite set of alleles at locus $l$,
$p_l : A_l \to \mathbb{R}$ real allele weights and $G_l(i, j)$ real genotypic values of the ordered
one-locus genotypes $(i, j)$. Let $\delta_l$ be the one-locus [dominance deviations](dom-dev.md) of
$p_l$ and $G_l$. The multilocus dominance variance is the weighted sum of squares of the summed
dominance deviations:

$$V_D = \sum_g f(g) \Bigl(\sum_{l \in L} \delta_l(i_l, j_l)\Bigr)^2,$$

summed over all ordered multilocus genotypes $g$, with $g_l = (i_l, j_l)$, with their
[weight](geno-freq.md) $f(g) = \prod_l p_l(i_l)\, p_l(j_l)$. When every $p_l$ is a probability
vector, the summed dominance deviation has mean $0$ under these weights, so $V_D$ is its variance.
