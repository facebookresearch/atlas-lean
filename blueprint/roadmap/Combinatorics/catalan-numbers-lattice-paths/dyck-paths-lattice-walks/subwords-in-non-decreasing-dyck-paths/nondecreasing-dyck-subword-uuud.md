# Subword $UUUD$ in non-decreasing Dyck paths

Let $F_{UUUD}(x, y) \in \mathbb{Z}[y][[x]]$ be
the bivariate generating function with constant term $0$ in which, for $n \ge 1$, the coefficient
of $x^n$ is the sum of $y^{k(P)}$ over the non-decreasing Dyck paths $P$ of semilength $n$, where
$k(P)$ is the number of occurrences of the subword $UUUD$ in $P$. Let $d_{UUUD}(n)$ be the total
number of occurrences of $UUUD$ over all non-decreasing Dyck paths of semilength $n$, let
$D_{UUUD}(x) = \sum_{n \ge 0} d_{UUUD}(n) x^n \in \mathbb{Z}[[x]]$, and let $F_n$ and $L_n$ denote
the Fibonacci and Lucas numbers. Then
$(1 - 3x + x^2 + (3 - 3y) x^3 - 2(1 - y) x^4) F_{UUUD}(x, y) = (1 - x)(x + x^3 (y - 1))$,
$(1 + x(x - 3))^2 D_{UUUD}(x) = (x - 1)^2 x^3 (x + 1)$, and for every $n \ge 3$,
$d_{UUUD}(n) = n F_{2n-5} - L_{2n-6}$.

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 12 (`jis-2025-25.1.6-thm-12`).
