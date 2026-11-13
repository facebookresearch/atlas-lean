# Step difference

For natural numbers $m, n$ and a real function $P(x, y)$ of two real
variables, let $l = \gcd(m \mathbin{\dot-} 1, n)$, where $m \mathbin{\dot-} 1$ is subtraction
truncated at $0$ (so $l = n$ when $m = 0$). The step difference of $P$ for the sector of slope
$n/m$ is $k = P((m - 1)/l, n/l) - P(0, 0)$, with $m - 1$ here the real difference and division
by $l = 0$ read as $0$: the change $P(x + (m - 1)/l, y + n/l) - P(x, y)$ of $P$ between
consecutive steps of a staircase of the sector, evaluated at the base point $(0, 0)$.

For every polynomial of Stanton's form (Theorem 2 of the source) this difference does not
depend on the base point, which is how the source defines $k$.

## Sources

- Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of R^2*, INTEGERS 25 (2025), Article A81, Section 2 (definition of `k`).
