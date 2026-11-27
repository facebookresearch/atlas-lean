# Chi-square regime: every expected genotype count at least c

For a real $c$, a natural number $N$ and real genotype counts $n$, the large-sample regime holds
when every expected genotype count is at least $c$:

$$c \le N \pi_i(\hat p) \quad \text{for } i = 0, 1, 2,$$

with the [Hardy–Weinberg proportions](hwe-prob.md) $\pi(p) = ((1 - p)^2, 2p(1 - p), p^2)$ at the
[sample allele frequency](allele-freq-hat.md) $\hat p$ of $n$; these are the denominators of the
[fitted Hardy–Weinberg statistic](hwe-stat.md). Cochran's finite-sample rule takes $c = 5$. The
[limit theorem](tendsto-in-distribution-hwe-stat.md) fixes $0 < p < 1$ and lets $N \to \infty$,
which sends every expected count to infinity.
