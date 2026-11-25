# Explicit bounds for incomplete cubic exponential sums

Let $p \ge 3$ be a prime, write
$e_p(t) = e^{2\pi i t/p}$ and $\delta_p = \frac{1.0661}{\log \log p}$, let $a, b, c$ be integers
with $p \nmid a$, let $B$ be a positive integer, and put
$S = \sum_{x=1}^{B} e_p(a x^3 + b x^2 + c x)$. If $B < \sqrt{p/2}$, then
$|S| \le 1.1 \, B^{1/4} p^{1/4 + \delta_p/4} (\log p)^{1/4}$. If $\sqrt{p/2} < B \le p$, then
$|S| \le 1.38 \, (1 + p/B^2)^{1/4} B^{3/4} p^{\delta_p/2} (\log p)^{1/4}$.

The hypothesis $p \ge 3$ makes $\log \log p > 0$. For $p = 2$, $f(x) = x^3 + x$ and $B = 2$,
the sum equals $2$ while the second bound is below $0.86$.

## Sources

- Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25 (2025), Article A48, Theorem 1.3.
