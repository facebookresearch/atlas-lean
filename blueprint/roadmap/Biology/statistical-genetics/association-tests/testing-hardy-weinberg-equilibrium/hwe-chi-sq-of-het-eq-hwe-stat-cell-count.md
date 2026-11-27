# Heterozygote-count statistic of a sample equals its table statistic

Let $X_0, X_1, \dots : \Omega \to \{0, 1, 2\}$ be the genotype classes (numbers of copies of $A$) of
successive individuals, $N$ a natural number and $\omega \in \Omega$. Then the
[heterozygote-count statistic](hwe-chi-sq-of-het.md) at the sample size $N$, the observed allele
count $\sum_{m < N} X_m(\omega)$ and the observed heterozygote count $\#\{m < N : X_m(\omega) = 1\}$
equals the [fitted Hardy–Weinberg statistic](hwe-stat.md) of the genotype counts
$n_i = \#\{m < N : X_m(\omega) = i\}$ of the first $N$ individuals. No measurability or probability
is involved.
