# At a polymorphic locus the fitted statistic tends in law to χ²₁

Let $P$ be a probability measure on $\Omega$ and let the genotype classes
$X_0, X_1, \dots : \Omega \to \{0, 1, 2\}$ of successive individuals be mutually independent and
identically distributed under $P$, with $P(X_0 = i) = \pi_i(p)$ for every class $i$, where
$\pi(p) = ((1 - p)^2, 2p(1 - p), p^2)$ are the [Hardy–Weinberg proportions](hwe-prob.md) at an
allele frequency $0 < p < 1$. Write $n_i(N) = \#\{m < N : X_m = i\}$ for the genotype counts of the
first $N$ individuals. Let $Z$ be a real random variable on a probability space with the chi-square
law with one degree of freedom. Then the [fitted Hardy–Weinberg statistic](hwe-stat.md) of the first
$N$ individuals,

$$
X^2\bigl(N, n(N)\bigr) = \sum_{i = 0}^{2}
\frac{\bigl(n_i(N) - N \pi_i(\hat p)\bigr)^2}{N \pi_i(\hat p)},
$$

with $\hat p$ the [sample allele frequency](allele-freq-hat.md) of $n(N)$, converges in distribution
to $Z$ as $N \to \infty$ (three classes with two free probabilities, one fitted parameter). The
condition $0 < p < 1$ is needed: at a
[monomorphic locus](not-tendsto-in-distribution-hwe-stat-of.md) the statistic has no such limit.
