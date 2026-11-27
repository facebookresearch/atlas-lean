# Closed form of the first-coalescence times

Let $\eta$ be the [size function](size-fn.md) of a [piecewise-constant history](piecewise-history.md) with $K \ge 1$ pieces, sizes $\nu_j$ and start times $s_j$, and let $m \ge 2$ be a natural number, $a = \binom{m}{2}$. Then the [first-coalescence time](first-coal-mean.md) satisfies

$$a\, c_m(\eta) = \nu_0 + \sum_{j=1}^{K-1} (\nu_j - \nu_{j-1})\, e^{-a R_\eta(s_j)},$$

with the [cumulative rate](cum-rate.md) $R_\eta$. In particular the integral defining $c_m$ converges.
