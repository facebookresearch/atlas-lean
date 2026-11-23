# Regret of Hedge for losses in the unit interval

Let $\eta > 0$ and let $\ell_1, \dots, \ell_T \in [0, 1]^n$. Hedge started from unit weights satisfies, for every expert $i$,

$$\sum_{t=1}^T \sum_j x_t(j) \ell_t(j) - \sum_{t=1}^T \ell_t(i) \le \eta T + \frac{\log n}{\eta}.$$

This is the second-order bound with $\ell_t(j)^2 \le 1$.

## Informally uses

- [The second-order Hedge bound](alg-loss-le-sq.md): builds on.
- [Summed second moments over $T$ rounds](alg-sq-le-length.md): builds on.

## Sources

- E. Hazan, *Introduction to Online Convex Optimization*, arXiv:1909.05207 (v1–v3 number the second-order bound Theorem 1.5, Section 1.3.3)
