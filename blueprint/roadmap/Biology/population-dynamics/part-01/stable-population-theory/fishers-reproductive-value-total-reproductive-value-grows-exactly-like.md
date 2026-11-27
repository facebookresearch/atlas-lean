# Fisher's reproductive value grows exactly exponentially

Let $l : [0, \infty) \to (0, 1]$ be a differentiable survivorship with $l(0) = 1$ and mortality $\mu = -l'/l$, let $m \ge 0$ be the age-specific fertility, and let $r$ be the root of the Euler–Lotka equation $\int_0^\infty e^{-ra} l(a) m(a)\, da = 1$. Fisher's reproductive value is

$$v(x) = \frac{e^{rx}}{l(x)} \int_x^\infty e^{-ry} l(y) m(y)\, dy$$

(Fisher 1930, Ch. II; Caswell 2019, eq. (3.4)). Differentiating gives $v(0) = 1$ and $v'(x) = (\mu(x) + r)\, v(x) - m(x)$. If the age density $n(x, t)$ solves the McKendrick–von Foerster equation $\partial_t n + \partial_x n = -\mu n$ with births $n(0, t) = \int_0^\infty m(x) n(x, t)\, dx$, and $n(x, t) v(x) \to 0$ as $x \to \infty$ with enough integrability to differentiate under the integral, then the total reproductive value $V(t) = \int_0^\infty n(x, t) v(x)\, dx$ satisfies

$$V'(t) = \int_0^\infty (-\partial_x n - \mu n) v\, dx = n(0, t) v(0) + \int_0^\infty n\,(v' - \mu v)\, dx = n(0, t) + \int_0^\infty n\,(r v - m)\, dx = r V(t),$$

by integration by parts and the birth condition, so $V(t) = V(0) e^{rt}$ exactly, for every initial age distribution.

## Expansion

1. The model: survivorship, mortality and fertility, the characteristic root $r$, and the McKendrick–von Foerster equation with the renewal boundary condition.
2. The definition of $v$ and the identities $v(0) = 1$ and $v' = (\mu + r) v - m$.
3. The computation of $V'$ by integration by parts, using the boundary condition at $0$ and the decay at infinity.
4. The regularity and decay hypotheses on $n$ and $v$ under which the computation is valid.
5. The discrete-age analogue (the left Perron eigenvector of the [Leslie matrix](../../leslie-matrix-model/leslie-matrix.md)), as a separate statement.

## Sources

- H. Caswell, *Sensitivity Analysis: Matrix Methods in Demography and Ecology*, Springer, 2019, Sec. 3.2, eqs. (3.1)–(3.4). <https://doi.org/10.1007/978-3-030-10534-1>
- Original result: R. A. Fisher, *The Genetical Theory of Natural Selection*, Clarendon Press, Oxford, 1930. <https://doi.org/10.5962/bhl.title.27468> The definition of reproductive value is in Chapter II.
