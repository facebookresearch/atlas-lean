# Ramanujan's integral for $\varphi(x) - 1$ (Chapter 8, Entry 12)

Let $x$ be a complex
number with $\operatorname{Re} x > 1$. For real $u$ and complex $s$ put $P_s(u) = 0$ if $u = 0$
and $P_s(u) = e^{s \log |u|}$ otherwise, and define $K_x(0) = 0$, $K_x(1) = 0$ and
$K_x(u) = \frac{P_{x-2}(u)\,(1 - u)^2}{1 - P_x(u)}$ for every other real $u$, the quotient being
taken to be $0$ at $u = -1$, where its denominator vanishes. Let
$\varphi(x) = 1 + \sum_{k \ge 1} \frac{2}{(kx)^3 - kx}$. Then $(kx)^3 - kx \ne 0$ for every
positive integer $k$; the series $\sum_{k \ge 1} \frac{2}{(kx)^3 - kx}$ converges
unconditionally; $K_x(0) = 0$ and $K_x(1) = 0$; for every $u \in (0, 1)$,
$1 - P_x(u) \ne 0$ and $K_x(u) = \frac{P_{x-2}(u)\,(1 - u)^2}{1 - P_x(u)}$; $K_x$ is integrable
on $[0, 1]$; and

$$\int_0^1 K_x(u)\,du = \varphi(x) - 1.$$

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.
