# Cochran's minimum-variance theorem for weighted averages

Let $\mu$ be a probability measure on $\Omega$ and $X_1, \dots, X_k : \Omega \to \mathbb{R}$ pairwise independent, square-integrable estimates with positive variances $v_i = \mathrm{Var}(X_i) > 0$, and let $w$ be the [inverse-variance weights](inverse-variance-weights.md) of $v$. Then the inverse-variance-weighted average has variance

$$\mathrm{Var}\Big(\sum_i w_i X_i\Big) = \Big(\sum_j v_j^{-1}\Big)^{-1},$$

and for every $c \in \mathbb{R}^k$ with $\sum_i c_i = 1$,

$$\Big(\sum_j v_j^{-1}\Big)^{-1} \le \mathrm{Var}\Big(\sum_i c_i X_i\Big).$$

## Sources

- W. G. Cochran, *The combination of estimates from different experiments*, Biometrics 10 (1954), 101–129.
