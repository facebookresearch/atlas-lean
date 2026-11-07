# Explicit upper bound in Mandl's inequality

Let $p_k$ denote the $k$-th prime, so that
$p_1 = 2$. For every integer $n \ge 64497259289$, put $\ell = \log n$, $L = \log p_n$,
$M(n) = \frac{n p_n}{2} - \sum_{k=1}^{n} p_k$,

$$\tau = 34.6L^3 + 205.592008L^2 + 1420.426661948448L + 28890.293784512888$$

and

$$\Omega(n) = \frac{\ell^2}{4L} + \frac{3.848668\,\ell^2}{4L^2} - \frac{\ell}{4} +
\frac{\log \ell}{4} + \frac{\tau\,\ell^2}{8L^6}.$$

Then

$$M(n) < \frac{n^2}{4} + \frac{n^2}{4\ell} - \frac{n^2 \log \ell}{4\ell^2} +
\frac{\Omega(n)\, n^2}{\ell^2}.$$

## Sources

- Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*, INTEGERS 25 (2025), Article A58, Proposition 4 (`integers-2025-A58-prop-4`).
