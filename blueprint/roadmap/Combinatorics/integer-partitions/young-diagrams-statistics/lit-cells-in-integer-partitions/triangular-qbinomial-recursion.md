# Recursion for triangular $q$-binomial coefficients

The triangular $q$-binomial
coefficients $t[r, s] \in \mathbb{Z}[[q]]$ satisfy the recursion
$t[r, s] = q^s \sum_{i=0}^{s} t[r - 1, i]$ for all natural numbers $r \ge 1$ and $s \le r$,
together with the initial conditions $t[1, 1] = q$, $t[2, 1] = q(1 + q)$, $t[r, 0] = 1$ for
every $r$, and $t[r, s] = 0$ whenever $r < s$.

The recursion is stated for $s \le r$ only: for $s > r$ the left side is $0$, while the right
side is $q^s \sum_{i=0}^{r-1} t[r - 1, i] \ne 0$; for example $t[1, 2] = 0$ but
$q^2 (t[0, 0] + t[0, 1] + t[0, 2]) = q^2$.

## Sources

- Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer Partitions*, INTEGERS 24 (2024), Article A56, Proposition 3, eqs. (9), (10).
