# Subword $UUU$ in non-decreasing Dyck paths

Let $F_{UUU}(x, y) \in \mathbb{Z}[y][[x]]$ be
the bivariate generating function with constant term $0$ in which, for $n \ge 1$, the coefficient
of $x^n$ is the sum of $y^{k(P)}$ over the non-decreasing Dyck paths $P$ of semilength $n$, where
$k(P)$ is the number of occurrences of the subword $UUU$ in $P$ (overlapping occurrences counted
separately). Let $d_{UUU}(n)$ be the total number of occurrences of $UUU$ over all non-decreasing
Dyck paths of semilength $n$, let $D_{UUU}(x) = \sum_{n \ge 0} d_{UUU}(n) x^n \in \mathbb{Z}[[x]]$,
and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$(1 - x(2 + y) + x^2 y) F_{UUU}(x, y) = (1 - xy) x$, $(1 - 3x + x^2)^2 D_{UUU}(x) = x^3$, and
for every $n \ge 1$, $10\, d_{UUU}(n) = -(5n + 4) F_{2n} + 3n L_{2n}$.

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 4 (`jis-2025-25.1.6-thm-4`).
