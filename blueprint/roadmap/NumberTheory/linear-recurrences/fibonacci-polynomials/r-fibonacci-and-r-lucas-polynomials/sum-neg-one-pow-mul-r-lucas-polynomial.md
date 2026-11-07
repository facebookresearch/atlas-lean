# Alternating sum of $r$-Lucas polynomials

Let $K$ be a field, let $r \ge 1$ and $s$ be
natural numbers, let $x, y \in K$ with $1 + x + (-1)^r y \ne 0$, and write $V_j$ for the
$r$-Lucas polynomial of type $s$, $V_j = V^{(r,s)}_j(x, y)$. Then for every natural number
$n \ge r - 1$,

$$
\sum_{j=1}^{n} (-1)^j V_j =
\frac{1 - (-1)^r s y + (-1)^n V_{n+1} + (-1)^r y \sum_{j=1}^{r} (-1)^{n-r+j} V_{n-r+j}}
{1 + x + (-1)^r y} - 1.
$$

For $n < r - 1$ the right side involves $V$ at negative indices.

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Corollary 5 (`integers-2025-A38-cor-5`).
