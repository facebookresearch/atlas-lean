# Multilocus half-sib covariance

Let $L$ be a finite set of loci, $A_l$ a finite set of alleles at locus $l$,
$p_l : A_l \to \mathbb{R}$ real allele weights and $G_l(i, j)$ real genotypic values of the ordered
one-locus genotypes $(i, j)$. Let $\mu$ be the [multilocus mean](multi-mean.md). A configuration $x$
gives every locus $l$ the common parent's ordered genotype $(i_l, j_l)$, the genes $k_l$ and $m_l$
from two unrelated mates, and choices $b_l, b'_l \in \{1, 2\}$ of the parental gene transmitted to
each offspring: $t_l = i_l$ if $b_l = 1$ and $t_l = j_l$ if $b_l = 2$, and likewise $t'_l$ from
$b'_l$. Put

$$
C_{HS} = \sum_x \prod_{l \in L} \frac{p_l(i_l)\, p_l(j_l)\, p_l(k_l)\, p_l(m_l)}{4}
\Bigl(\sum_{l} G_l(t_l, k_l) - \mu\Bigr) \Bigl(\sum_{l} G_l(t'_l, m_l) - \mu\Bigr).
$$

When every $p_l$ is a probability vector, it is the covariance of the genotypic values of two half
sibs: the common parent is drawn in Hardy–Weinberg proportions and linkage equilibrium and transmits
to each offspring, at each locus independently, one of its two genes with probability $1/2$, and the
offspring's other genes come from two unrelated mates.
