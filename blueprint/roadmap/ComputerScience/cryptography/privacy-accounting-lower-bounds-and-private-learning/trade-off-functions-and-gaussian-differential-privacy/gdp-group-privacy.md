# Group privacy for Gaussian differential privacy

If a mechanism is $\mu$-GDP with respect to datasets differing in one record, then for every $k \ge 1$ it is $k\mu$-GDP with respect to datasets differing in at most $k$ records. More generally, $f$-DP implies $\big(1 - (1 - f)^{\circ k}\big)$-DP for groups of size $k$, where $\circ k$ denotes $k$-fold composition of functions, and for $G_\mu$ this evaluates exactly to $G_{k\mu}$.

## Proof sketch

Connect two datasets at distance $k$ by a chain of $k$ neighbouring steps. Testing the endpoints is at least as hard as the chained testing problem, whose trade-off function is obtained by composing the single-step bounds as functions: a type I error $\alpha$ propagates to type II error at most $1 - f(\dots)$ at each step. For Gaussians, $1 - G_\mu(1 - \cdot)$ composes as a shift of the mean, and $k$ shifts by $\mu$ give $G_{k\mu}$.

## Depends on

- [Gaussian differential privacy](gaussian-differential-privacy.md)

## Proof depends on

- [Group privacy, approximate case](../../differential-privacy/group-approx.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
