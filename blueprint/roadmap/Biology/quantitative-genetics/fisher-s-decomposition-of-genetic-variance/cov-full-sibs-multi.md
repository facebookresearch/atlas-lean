# Multilocus full-sib covariance

Let $L$ be a finite set of loci, $A_l$ a finite set of alleles at locus $l$,
$p_l : A_l \to \mathbb{R}$ real allele weights and $G_l(i, j)$ real genotypic values of the ordered
one-locus genotypes $(i, j)$. Let $\mu$ be the [multilocus mean](multi-mean.md). A configuration $x$
gives every locus $l$ the sire's ordered genotype $(i_l, j_l)$, the dam's ordered genotype
$(k_l, m_l)$, and choices $b_l, b'_l, e_l, e'_l \in \{1, 2\}$: the first offspring receives $t_l$
from the sire and $s_l$ from the dam, and the second $t'_l$ and $s'_l$, where $t_l = i_l$ if
$b_l = 1$ and $t_l = j_l$ if $b_l = 2$, $s_l = k_l$ if $e_l = 1$ and $s_l = m_l$ if $e_l = 2$, and
likewise $t'_l$ from $b'_l$ and $s'_l$ from $e'_l$. Put

$$
C_{FS} = \sum_x \prod_{l \in L} \frac{p_l(i_l)\, p_l(j_l)\, p_l(k_l)\, p_l(m_l)}{16}
\Bigl(\sum_{l} G_l(t_l, s_l) - \mu\Bigr) \Bigl(\sum_{l} G_l(t'_l, s'_l) - \mu\Bigr).
$$

When every $p_l$ is a probability vector, it is the covariance of the genotypic values of two full
sibs: the unrelated sire and dam are drawn in Hardy–Weinberg proportions and linkage equilibrium,
and each transmits to each offspring, at each locus independently, one of its two genes with
probability $1/2$.
