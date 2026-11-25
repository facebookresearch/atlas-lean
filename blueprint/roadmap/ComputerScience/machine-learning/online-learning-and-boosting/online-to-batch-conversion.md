# Online-to-batch conversion

Let $K$ be a convex set and $\ell(\cdot, z)$ convex on $K$ for every $z$, with $L_D(x) = \mathbb{E}_{z \sim D}\ell(x, z)$
finite on $K$. Suppose an online algorithm, choosing $x_t \in K$ as a function of $z_1, \dots, z_{t-1}$ only, has
regret at most $R_T$ against every $u \in K$ on every sequence. If $z_1, \dots, z_T$ are i.i.d. from $D$ and
$\bar x = \frac1T \sum_t x_t$, then $\mathbb{E}[L_D(\bar x)] - \inf_{u \in K} L_D(u) \le R_T / T$, by Jensen's
inequality and $\mathbb{E}[\ell(x_t, z_t) \mid z_1, \dots, z_{t-1}] = L_D(x_t)$. If the losses take values in
$[0, 1]$, then with probability at least $1 - \delta$,
$L_D(\bar x) - \inf_{u \in K} L_D(u) \le R_T/T + \sqrt{8\log(2/\delta)/T}$ by Azuma's inequality.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Online convex optimization and projected OGD regret.

## Depends on

- [Expected risk](../generalization-bounds-and-concentration/risk.md)

## Sources

- E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207, Chapter 9: Theorem 9.5 (online-to-batch conversion for convex losses) with Azuma's inequality, Theorem 9.7. <https://arxiv.org/pdf/1909.05207>
