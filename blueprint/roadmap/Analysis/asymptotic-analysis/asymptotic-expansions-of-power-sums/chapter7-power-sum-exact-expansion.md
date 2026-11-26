# Euler–Maclaurin expansion of power sums with constant ζ(-r)

Let $r \in \mathbb{C}$ with $r \ne -1$, and let $N \ge 1$ and $n \ge 2$ be integers with $\operatorname{Re} r < 2N$.
Then, with principal complex powers,

$$\sum_{k=1}^{n} k^r = \zeta(-r) + \frac{n^{r+1}}{r+1} + \frac{n^r}{2}
+ \sum_{j=1}^{N} \frac{B_{2j}}{(2j)!}\, (r)_{2j-1}\, n^{r-2j+1}
- \frac{(r)_{2N+1}}{(2N+1)!} \int_n^\infty x^{r-2N-1}\, B_{2N+1}(\{x\})\, dx,$$

where $(r)_q = r(r-1)\cdots(r-q+1)$ is the falling product, $B_{2j}$ are the Bernoulli numbers, $B_{2N+1}(\{x\})$ is
the Bernoulli polynomial of degree $2N+1$ at the fractional part of $x$, and the integral converges because
$\operatorname{Re} r < 2N$.
