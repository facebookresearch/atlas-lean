# A square-splitting divisor function and its Euler product

Let
$\alpha \in \mathbb{C}$, let $\sigma_\beta(m) = \sum_{d \mid m} d^\beta$ for $\beta \in \mathbb{C}$
(complex powers), and let $f(n) = \sigma_\alpha(u(n))\,\sigma_{2\alpha}(v(n))$, where $u(n)$ is
the product of the primes dividing $n$ to an odd power and $v(n)$ is the positive integer with
$n = u(n)\,v(n)^2$. Then $f(1) = 1$ and $f(mn) = f(m)\,f(n)$ for all coprime $m$ and $n$. For
every prime $p$ and every $b \ge 0$, $f(p^{2b}) = \sum_{j=0}^{b} p^{2j\alpha}$ and
$f(p^{2b+1}) = (1 + p^\alpha) \sum_{j=0}^{b} p^{2j\alpha}$. For every complex $s$ with
$\operatorname{Re} s > \max(1, 1 + \operatorname{Re} \alpha)$, for every prime $p$

$$\sum_{k \ge 0} \frac{f(p^k)}{p^{ks}}
= \frac{1 + p^{-s} + p^{-(s-\alpha)}}{(1 - p^{-2s})(1 - p^{-(2s-2\alpha)})},$$

the series $\sum_{n \ge 1} f(n)\,n^{-s}$ converges absolutely, and

$$\sum_{n \ge 1} \frac{f(n)}{n^s}
= \zeta(2s)\,\zeta(2s - 2\alpha) \prod_p \left(1 + p^{-s} + p^{-(s-\alpha)}\right).$$

The paper identifies $f$ with its divisor function $\sigma_{\star,\alpha}$; that identification is
not part of this statement.

## Sources

- Champak Talukdar and Helen K. Saikia, *A Square-Splitting A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 6.
