# Sum of the first $n$ $r$-Lucas polynomials

Let $K$ be a field, let $r \ge 1$ and $s$ be
natural numbers, let $x, y \in K$ with $1 - x - y \ne 0$, and write $V_j$ for the $r$-Lucas
polynomial of type $s$, $V_j = V^{(r,s)}_j(x, y)$. Then for every natural number $n$ with
$n \ge 1$ and $n \ge r - 1$,

$$
\sum_{j=1}^{n} V_j = \frac{1 + s y - V_{n+1} - y \sum_{j=1}^{r} V_{n-r+j}}{1 - x - y} - 1.
$$

The paper states $n \ge 1$; for $n < r - 1$ the right side involves $V$ at negative indices.

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Corollary 4 (`integers-2025-A38-cor-4`).
