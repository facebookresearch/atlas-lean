# At a polymorphic locus the heterozygote-count statistic tends to χ²₁

Let $P$ be a probability measure on $\Omega$ and let the genotype classes
$X_0, X_1, \dots : \Omega \to \{0, 1, 2\}$ of successive individuals be mutually independent and
identically distributed under $P$, with $P(X_0 = i) = \pi_i(p)$ for every class $i$, where
$\pi(p) = ((1 - p)^2, 2p(1 - p), p^2)$ are the [Hardy–Weinberg proportions](hwe-prob.md) at an
allele frequency $0 < p < 1$. Let $Z$ be a real random variable on a probability space with the
chi-square law with one degree of freedom. Then the
[heterozygote-count statistic](hwe-chi-sq-of-het.md) behind the
[asymptotic p-value](asymptotic-hwepvalue.md), at the sample size $N$, the observed allele count
$\sum_{m < N} X_m$ and the observed heterozygote count $\#\{m < N : X_m = 1\}$, converges in
distribution to $Z$ as $N \to \infty$. The limit says nothing about a fixed small sample: in the
[sparse model](not-is-valid-pvalue-asymptotic-hwepvalue.md) the asymptotic p-value is not valid.
