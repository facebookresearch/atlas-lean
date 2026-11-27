# Genome-wide error control of the permutation maximum test

Keep the notation of the [permutation maximum threshold](permutation-maximum-threshold.md). Assume the global null hypothesis $H_0$: conditionally on the genotypes $G$, the trait vector $y$ is exchangeable, that is $y_\pi \overset{d}{=} y$ given $G$ for every fixed permutation $\pi$ (for instance $y_1, \dots, y_n$ are i.i.d. and independent of $G$, so no position carries a trait locus).

Let $\pi_1, \dots, \pi_M$ be i.i.d. uniform random permutations independent of $(y, G)$, with $T^{\max}_m = T^{\max}(y_{\pi_m}, G)$ as before. Declare a position $\ell \in L$ significant when

$$\frac{1 + \#\{1 \le m \le M : T^{\max}_m \ge T_\ell(y, G)\}}{M + 1} \le \alpha .$$

Then for every $\alpha \in [0, 1]$ this rule makes at least one false declaration with probability at most $\alpha$ under $H_0$, whatever the number of positions and the dependence among the $T_\ell$.

## Depends on

- [Permutation threshold for the maximum statistic of a genome scan](permutation-maximum-threshold.md)

## Proof depends on

- [Validity of Monte Carlo permutation p-values](../../../Probability/hypothesis-testing/permutation-tests/is-valid-pvalue-monte-carlo-permutation.md)

## Expansion

Let the symmetric group $S_n$ act on the data $(y, G)$ by permuting $y$ and fixing $G$. Under $H_0$ the law of $(y, G)$ is invariant under this action, so validity of Monte Carlo permutation p-values, applied with $T = T^{\max}$ and $B = M$, shows that

$$p = \frac{1 + \#\{1 \le m \le M : T^{\max}_m \ge T^{\max}_0\}}{M + 1}, \qquad T^{\max}_0 = T^{\max}(y, G),$$

satisfies $\Pr_{H_0}(p \le \alpha) \le \alpha$. Every $\ell$ has $T_\ell(y, G) \le T^{\max}_0$, so $\#\{m : T^{\max}_m \ge T_\ell(y, G)\} \ge \#\{m : T^{\max}_m \ge T^{\max}_0\}$, and declaring $\ell$ implies $p \le \alpha$. Under $H_0$ every declaration is false, so the family-wise error is at most $\Pr_{H_0}(p \le \alpha) \le \alpha$. The "$1 +$" term matters: declaring $\ell$ when $T_\ell$ reaches the $\lceil (1 - \alpha)(M + 1) \rceil$-th smallest of $T^{\max}_0, \dots, T^{\max}_M$ has family-wise error at least $(\lfloor \alpha (M + 1) \rfloor + 1)/(M + 1) > \alpha$ (with equality when there are no ties), which is $0.10$ for $M = 19$ and $\alpha = 0.05$; the plain percentile of $T^{\max}_1, \dots, T^{\max}_M$ used in practice attains the level only as $M \to \infty$.

## Sources

- G. A. Churchill and R. W. Doerge, "Empirical threshold values for quantitative trait mapping", Genetics 138 (1994), 963–971, <https://doi.org/10.1093/genetics/138.3.963> (PMC1206241). The finite-$M$ bound is the standard Monte Carlo randomization-test bound (B. Phipson and G. K. Smyth, *Permutation p-values should never be zero*, Stat. Appl. Genet. Mol. Biol. 9 (2010), Article 39), applied here to $T^{\max}$.
