# Asymptotic expansion of the Lambert series $\sum_k 1/(e^{kx}+1)$

Let $x > 0$ be real
and let $n \ge 1$ be an integer. Let $B_m$ be the $m$-th Bernoulli number and let
$D_n(x) = \sum_{k=1}^{n} \frac{(2^{2k} - 1) \, B_{2k}^2 \, x^{2k-1}}{2k \, (2k)!}$. Then the
series $\sum_{k=1}^{\infty} \frac{1}{e^{kx} + 1}$ is summable, and its sum $T(x)$ satisfies
$\left| T(x) - \left( \frac{\log 2}{x} - \frac14 + D_n(x) \right) \right|
\le \frac{|B_{2n} B_{2n+2}| \, x^{2n}}{(2n)!} \left( \frac{x^2}{4\pi^2} + \frac{\pi^2}{6} +
2^{2n+1} \left( \frac{x^2}{\pi^2} + \frac{\pi^2}{6} \right) \right)$.

The proof writes this series as the series $\sum_k 1/(e^{kx}-1)$ minus twice the same series
at $2x$, and applies the remainder bound for $\sum_k 1/(e^{kx}-1)$.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
