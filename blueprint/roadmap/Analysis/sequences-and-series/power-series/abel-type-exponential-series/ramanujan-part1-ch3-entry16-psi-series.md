# Ramanujan's $\psi$-series (Chapter 3, Entry 16)

For natural numbers $r$, $k$ and a complex
number $n$ define $\psi(r, k, n)$ recursively by $\psi(0, 1, n) = 1$, $\psi(0, k, n) = 0$ for
$k \ne 1$, and

$$\psi(r + 1, k, n) = (n - r - k)\, \psi(r, k, n) + (r + k - 1)\, \psi(r, k - 1, n),$$

where the last term is read as $0$ when $k = 0$. Let $r$ be a natural number and let $n$, $u$ be
complex numbers with $|u e^{1-u}| < 1$ and $|u| < 1$. Then the series

$$\sum_{j=0}^{\infty} \frac{(n + j)^{r+j}\, e^{-u(n+j)}\, u^j}{j!}$$

converges unconditionally to

$$\sum_{k=1}^{r+1} \frac{\psi(r, k, n)}{(1 - u)^{r+k}}.$$

The hypothesis $|u| < 1$ selects the component of $\{u : |u e^{1-u}| < 1\}$ containing $0$;
given $|u e^{1-u}| < 1$, it is equivalent to $\operatorname{Re} u < 1$. On the other component
the series converges to a different value.

Proof: Entry 12 gives absolute and locally uniform convergence, and termwise
differentiation gives the recurrence in Berndt (16.4)-(16.5). The Jensen-series
base case from Berndt (16.6) extends to the star-convex domain by analytic uniqueness.

## Sources

- Berndt, Ramanujan's Notebooks Part I, Chapter 3, construction and formulas (16.4)-(16.5), printed pp. 78-79 / PDF pp. 88-89.
