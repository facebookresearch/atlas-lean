# Number of points of valuation one modulo $p^2$

Let $p$ be a prime and let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$. Suppose that for all integers
$r, s \in \{0, \dots, p - 1\}$ with $p \mid f(r, s)$, the integers $f_x(r, s)$ and $f_y(r, s)$
are not both divisible by $p$. Let $m$ be the number of pairs $(r, s)$ with $0 \le r, s < p$ and
$p \mid f(r, s)$. Then the number of pairs $(x, y)$ with $0 \le x, y < p^2$, $p \mid f(x, y)$
and $p^2 \nmid f(x, y)$ is $m p (p - 1)$.

Without the hypothesis on $f_x$ and $f_y$ the count fails: for $f = x^2 - y^2$ and $p = 3$ one
has $m = 5$, but only $24$ pairs, not $30$, have valuation $1$.

## Sources

- Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Corollary 2 (`integers-2026-A82-cor-2`).
