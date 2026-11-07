# Explicit sum for the companion sequence $V^{(-r)}$

Let $K$ be a field of
characteristic zero, $r \ge 2$ and $n \ge 1$ natural numbers, $x \in K$ and $y$ a unit of
$K$, and let $V^{(-r)}_n(x, y)$ be the companion sequence of the $(-r)$-Fibonacci
polynomials. Then

$$V^{(-r)}_n(x, y) = \sum_{k} \frac{n}{n - rk} \binom{k - 1}{n - 1 - rk} y^{-k} \,
(-x)^{n - rk} + \varepsilon,$$

where the sum runs over the natural numbers $k \ge 1$ with $rk < n$, $\binom{a}{b}$ is the
binomial coefficient of natural numbers (zero when $b > a$), and $\varepsilon = r y^{-n/r}$ if
$r$ divides $n$ and $\varepsilon = 0$ otherwise.

The paper's range $\lfloor n/(r+1) \rfloor \le k \le \lfloor n/r \rfloor$ also admits $k = n/r$
(division by zero; that term is the $\varepsilon$ term) and, for $n \le r$, $k = 0$, whose term
$\binom{-1}{n-1}$ must be read as $0$ (with $\binom{-1}{j} = (-1)^j$, $r = 2$, $n = 1$ gives
$-x$ instead of $V^{(-r)}_1 = 0$); both are excluded.

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Theorem 7.
