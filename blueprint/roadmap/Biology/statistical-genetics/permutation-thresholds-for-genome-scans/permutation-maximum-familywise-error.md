# Genome-wide error control of the permutation maximum test

Keep the notation of the [permutation maximum threshold](permutation-maximum-threshold.md). Assume the global null hypothesis $H_0$: conditionally on the genotypes $G$, the trait vector $y$ is exchangeable, that is $y_\pi \overset{d}{=} y$ given $G$ for every fixed permutation $\pi$ (for instance $y_1, \dots, y_n$ are i.i.d. and independent of $G$, so no position carries a trait locus).

Let $T^{\max}_0 = T^{\max}(y, G)$ be the observed maximum, let $\pi_1, \dots, \pi_M$ be i.i.d. uniform random permutations independent of $(y, G)$, and define the Monte Carlo $p$-value

$$p = \frac{1 + \#\{m \le M : T^{\max}_m \ge T^{\max}_0\}}{M + 1}.$$

Then for every $\alpha \in [0, 1]$,

$$\Pr_{H_0}\bigl(p \le \alpha\bigr) \le \alpha .$$

Consequently the rule "declare every position $\ell$ with $T_\ell(y, G) \ge c$ significant", where $c$ is the $\lceil (1 - \alpha)(M + 1) \rceil$-th smallest of $T^{\max}_0, T^{\max}_1, \dots, T^{\max}_M$, makes at least one false declaration with probability at most $\alpha$ under $H_0$, whatever the number of positions and the dependence among the $T_\ell$.

## Expansion

Under $H_0$, condition on $G$ and on the multiset of trait values. Then $y, y_{\pi_1}, \dots, y_{\pi_M}$ are exchangeable (each is a uniformly random arrangement of the same multiset), so $T^{\max}_0, \dots, T^{\max}_M$ are exchangeable. The rank of $T^{\max}_0$ among the $M + 1$ values, with ties broken against rejection, is therefore stochastically no smaller than uniform on $\{1, \dots, M + 1\}$, which gives $\Pr(p \le \alpha) \le \lfloor \alpha (M + 1) \rfloor / (M + 1) \le \alpha$. A false declaration at any position implies $T^{\max}_0 \ge c$, which is the event $p \le \alpha$; so the family-wise error is bounded by $\alpha$. Without the "$1 +$" correction, the plain percentile of $T^{\max}_1, \dots, T^{\max}_M$ used in practice attains the level only as $M \to \infty$.

## Sources

- G. A. Churchill and R. W. Doerge, "Empirical threshold values for quantitative trait mapping", Genetics 138 (1994), 963–971, <https://doi.org/10.1093/genetics/138.3.963> (PMC1206241). The finite-$M$ exchangeability argument above is the standard Monte Carlo randomization-test bound, derived here.
