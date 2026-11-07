# The subword $DDD$ in non-decreasing Dyck paths

Let $F_{DDD}(x, y)$ and $D_{DDD}(x)$ be
the bivariate and univariate generating functions of the subword $DDD$ in non-decreasing Dyck
paths, let $d_{DDD}(n)$ be the total number of occurrences of $DDD$ over all non-decreasing Dyck
paths of semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then

$$(1 - x(1 + y) - x^2(1 - y)) (1 - x(1 + 2y) - x^2(1 - y - y^2)) F_{DDD}(x, y) =
x (1 - xy) (1 - 2xy - x^2(1 - y^2))$$

in $\mathbb{Z}[y][[x]]$,

$$(1 - 2x) (1 - 3x + x^2)^2 D_{DDD}(x) = x^3 (1 - 2x + x^2 - x^3)$$

in $\mathbb{Z}[[x]]$, and for every $n \ge 3$,

$$4 d_{DDD}(n) = (-8n + 10) F_{2n} + (4n - 6) L_{2n} + 2^n.$$

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 10 (`jis-2025-25.1.6-thm-10`).
