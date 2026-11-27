# Maximum likelihood over a finite family is Hellinger-consistent at rate exp(-n r^2)

Let $q_1, \dots, q_M$ ($M \ge 1$) be distributions on a countable set and let the data $x_1, \dots, x_n$ be i.i.d. from $p = q_{i^\ast}$ for some $i^\ast$. Let $\hat q$ be any maximizer of the likelihood $\prod_{j} q_i(x_j)$ over $i \in \{1,\dots,M\}$ (ties broken arbitrarily). Then for every $r \ge 0$,

$$
\Pr\bigl[h(p, \hat q) > r\bigr] \le (M-1)\,e^{-n r^2},
$$

where $h$ is the Hellinger distance with $h^2 = 1 - \mathrm{BC}$.

## Proof sketch

If $\hat q = q_i$ with $h(p,q_i) > r$, then $q_i$'s likelihood is at least that of $p$. By the likelihood-ratio Chernoff bound this has probability at most $e^{-n h^2(p, q_i)} \le e^{-nr^2}$ for each of the at most $M-1$ such candidates; a union bound finishes.

## Depends on

- [Maximum likelihood estimator](../../likelihood-and-maximum-likelihood-estimators/is-maximum-likelihood-estimator.md)
- [Hellinger distance](../../../convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Proof depends on

- [Likelihood-ratio Chernoff bound in Bhattacharyya and Hellinger form](likelihood-ratio-chernoff-bound.md)

## Sources

- Clément L. Canonne, "Topics and Techniques in Distribution Testing: A Biased but Representative Sample", Foundations and Trends in Communications and Information Theory, 2022.
- Alexandre B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
