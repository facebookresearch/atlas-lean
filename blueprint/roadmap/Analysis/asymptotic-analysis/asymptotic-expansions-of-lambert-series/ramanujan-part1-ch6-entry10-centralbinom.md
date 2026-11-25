# Asymptotic expansion of the Lambert series $\sum_k 1/(e^{kx}-1)$

Let $x > 0$ be real
and let $n \ge 1$ be an integer. Let $B_m$ be the $m$-th Bernoulli number, let $\gamma$ be the
Euler–Mascheroni constant, and let
$C_n(x) = \sum_{k=1}^{n} \frac{B_{2k}^2 \, x^{2k-1}}{2k \, (2k)!}$. Then the series
$\sum_{k=1}^{\infty} \frac{1}{e^{kx} - 1}$ is summable, and its sum $S(x)$ satisfies
$\left| S(x) - \left( \frac{\gamma}{x} - \frac{\log x}{x} + \frac14 - C_n(x) \right) \right|
\le \frac{|B_{2n} B_{2n+2}| \, x^{2n}}{(2n)!} \left( \frac{x^2}{4\pi^2} + \frac{\pi^2}{6} \right)$.

The proof applies the Euler–Maclaurin formula to the smooth Mittag-Leffler kernel and bounds
the periodic Bernoulli remainder by its Fourier series.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
