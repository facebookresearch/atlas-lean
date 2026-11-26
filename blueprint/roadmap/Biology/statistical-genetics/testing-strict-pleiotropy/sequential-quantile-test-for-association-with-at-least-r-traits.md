# Sequential quantile test for association with at least r traits

Let $H_0^r$ state that a variant affects at most $r-1$ of $K$ traits, against $H_a^r$: some set of at least $r$ traits has nonzero effects. For each of $p_0$ variants, sort its $K$ per-trait GWAS $p$-values, $p_{(1),j} \le \dots \le p_{(K),j}$. The *sequential quantile test* (SQT) at nominal family-wise level $\alpha$ proceeds for $r = 1,2,\dots$:

1. let $q$ be the number of variants still retained and set $c_r = \dfrac{\alpha}{q\,(K - r + 1)}$;
2. retain only the variants with $p_{(r),j} < c_r$; these are declared associated with at least $r$ traits.

The procedure stops when no variant survives (at $r_0$, no variant is associated with more than $r_0 - 1$ traits).

**Proposition 3.** The SQT controls the family-wise error rate for $H_0^r$ at level $\alpha$ asymptotically, at each iteration $r$.

## Depends on

- [Minimum-Wald intersection–union test for strict pleiotropy](minimum-wald-intersection-union-test-for-strict-pleiotropy.md)

## Expansion

Under $H_0^r$ at most $r-1$ effects are nonzero, so for $p_{(r),j}$ to be small at least one of the at least $K - r + 1$ null $p$-values must fall below the threshold; a Bonferroni bound over those $K - r + 1$ nulls gives the factor $K - r + 1$ (for $r = K$ this is the minimum-Wald test). The factor $q$ is a Bonferroni correction over the variants carried forward, and it shrinks as $r$ grows, so later stages test fewer variants at a less stringent threshold than a fixed genome-wide cutoff $\alpha/p_0$. The test uses only marginal $p$-values, so it is robust to the dependence among traits and is cheap for large $K$.

## Sources

- Eva Biswas, Nilanjan Chatterjee and Zheyu Wang, *Testing Procedures for Strict Pleiotropy in Genetic Association Studies*, arXiv:2610.00962 (2026). <https://doi.org/10.48550/arXiv.2610.00962> Section 2.3 (SQT algorithm and Proposition 3).
