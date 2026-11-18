# Asymptotic expansion of partial sums of powers times logarithms

Let $r > -1$ be a real
number. For a natural number $n$ write $\varphi_r(n) = \sum_{k=1}^{n} k^r \log k$ and
$S_r(n) = \sum_{k=1}^{n} k^r$, and for a natural number $m$ let
$D_m(r) = \sum_{j=0}^{m} \prod_{0 \le q \le m,\ q \ne j} (r - q)$, the derivative of
$r(r-1)\cdots(r-m)$ with respect to $r$. Let $B_j$ be the Bernoulli numbers and $\zeta$ the Riemann
zeta function. Then there is a real constant $C$ such that for every natural number $N$, as
$n \to \infty$ through the natural numbers,

$$
\varphi_r(n) - \log n \, \bigl(S_r(n) - \zeta(-r)\bigr) = C - \frac{n^{r+1}}{(r+1)^2} +
\sum_{k=1}^{N} \frac{B_{2k}}{(2k)!} D_{2k-2}(r) \, n^{r-2k+1} + O\bigl(n^{r-2N-1}\bigr).
$$

Moreover, if $r > 0$, then $\Gamma(r+1) > 0$, the series $\sum_{n \ge 1} \log n / n^{r+1}$
converges, and

$$
C = \frac{2\Gamma(r+1)\zeta(r+1)}{(2\pi)^{r+1}} \Bigl(\sin\frac{\pi r}{2} \Bigl(\log(2\pi) -
\frac{\Gamma'(r+1)}{\Gamma(r+1)}\Bigr) - \frac{\pi}{2} \cos\frac{\pi r}{2}\Bigr) +
\frac{2\Gamma(r+1)\sin\frac{\pi r}{2}}{(2\pi)^{r+1}} \sum_{n=1}^{\infty} \frac{\log n}{n^{r+1}}.
$$

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
