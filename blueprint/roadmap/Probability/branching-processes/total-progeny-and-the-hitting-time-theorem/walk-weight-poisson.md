# Walk weights for Poisson offspring

Let $r \ge 0$ and $k \le n$ be natural numbers, and let $p(j) = e^{-r} r^j / j!$ be the
Poisson($r$) weights. Then the [walk weight](walk-weight.md) is

$$W_p(k, n) = \frac{e^{-rn} (rn)^{n-k}}{(n-k)!} ,$$

since the sum of $n$ independent Poisson($r$) variables is Poisson($rn$).
