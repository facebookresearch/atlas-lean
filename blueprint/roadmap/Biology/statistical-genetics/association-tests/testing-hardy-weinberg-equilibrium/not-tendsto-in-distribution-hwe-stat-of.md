# At a monomorphic locus the fitted statistic does not tend to χ²₁

Let $P$ be a probability measure on $\Omega$, let the genotype classes
$X_0, X_1, \dots : \Omega \to \{0, 1, 2\}$ be identically distributed under $P$ with
$P(X_0 = i) = \pi_i(p)$ for the [Hardy–Weinberg proportions](hwe-prob.md) at $p = 0$ or $p = 1$, and
let $Z$ be a real random variable on a probability space with the chi-square law with one degree of
freedom. Then the [fitted Hardy–Weinberg statistic](hwe-stat.md) of the first $N$ individuals does
not converge in distribution to $Z$: it is
[almost surely $0$](hwe-stat-ae-eq-zero-of-monomorphic.md), so its limit in distribution is the
point mass at $0$. The condition $0 < p < 1$ of the
[limit theorem](tendsto-in-distribution-hwe-stat.md) cannot be dropped.
