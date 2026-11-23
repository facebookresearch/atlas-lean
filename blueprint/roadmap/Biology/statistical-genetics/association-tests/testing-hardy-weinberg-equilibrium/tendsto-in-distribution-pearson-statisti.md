# At a polymorphic locus with known frequency the statistic tends to χ²₂

Let $P$ be a probability measure on $\Omega$ and let the genotype classes
$X_0, X_1, \dots : \Omega \to \{0, 1, 2\}$ of successive individuals be mutually independent and
identically distributed under $P$, with $P(X_0 = i) = \pi_i(p)$ for every class $i$, where
$\pi(p) = ((1 - p)^2, 2p(1 - p), p^2)$ are the [Hardy–Weinberg proportions](hwe-prob.md) at an
allele frequency $0 < p < 1$. Write $n_i(N) = \#\{m < N : X_m = i\}$ for the genotype counts of the
first $N$ individuals, and let $Z$ be a real random variable on a probability space with the
chi-square law with two degrees of freedom. Then Pearson's statistic against the true proportions,

$$\sum_{i = 0}^{2} \frac{\bigl(n_i(N) - N \pi_i(p)\bigr)^2}{N \pi_i(p)},$$

converges in distribution to $Z$ as $N \to \infty$ (three classes, two degrees of freedom). With the
allele frequency estimated instead, the
[limit has one degree of freedom](tendsto-in-distribution-hwe-stat.md).
