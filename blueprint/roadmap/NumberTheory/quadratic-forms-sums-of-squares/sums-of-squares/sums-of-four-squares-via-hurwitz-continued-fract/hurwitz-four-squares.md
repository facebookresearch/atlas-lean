# Sums of four squares via Hurwitz continued fractions

Let $w$, $x$, $y$ be natural numbers
such that $w$ is odd and not a perfect square, $2x < w$, $2y < w$ and $w$ divides
$x^2 + y^2 + 1$. Expand $z = (x + yi)/w$ by the Hurwitz algorithm, with convergent numerators
$P_n$ and convergent denominators $Q_n$. Then there is exactly one natural number $n$ such that
$n + 1$ is a legal index for $z$, $|Q_n| \le \sqrt{w} < |Q_{n+1}|$, and, if $|Q_n| \ne \sqrt{w}$,
$w = |(x + yi) Q_n - w P_n|^2 + |Q_n|^2$.

When it holds, the last identity is a representation of $w$ as a sum of four squares.

## Sources

- Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued Fractions*, INTEGERS 24 (2024), Article A25, Theorem 1 (`integers-2024-A25-thm-1`).
