# Alternating sums of trinomial coefficients in an arithmetic progression

Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1 + t + t^2)^n$.
For natural numbers $n$, $x$, $b$ with $b$ even and $x < b$,

$$\sum_{k=0}^{2n} (-1)^k \binom{n}{x + bk}_2 = \frac{1}{b} \sum_{j=1}^{b}
\cos\frac{\pi(n - x)(1 + 2j)}{b} \left(1 + 2\cos\frac{\pi(2j + 1)}{b}\right)^n.$$

The paper sums over all $k \ge 0$ (the terms with $k > 2n$ vanish) and does not state
$x < b$; without it the identity fails: for $n = 3$ and $b = x = 2$ the left side is $1$ and
the right side is $0$.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Corollary 11 (`jis-2025-25.3.5-cor-11`).
