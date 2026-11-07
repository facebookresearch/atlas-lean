# Recurrence for the subword $U^mD$ in non-decreasing Dyck paths

Let $m \ge 1$. Let
$d_w(n)$ be the total number of occurrences of the subword $w$ over all non-decreasing Dyck paths
of semilength $n$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every
$n \ge m + 2$,

$$d_{U^mD}(n) = 3\,d_{U^mD}(n-1) - d_{U^mD}(n-2) + F_{2(n-m)-3} + m\,F_{2(n-m-1)};$$

moreover $d_{U^mD}(n) = 0$ for every $n < m$, $d_{U^mD}(m) = 1$, and $d_{U^mD}(m+1) = m + 2$.

The source states the recurrence for $n \ge m$, where $n = m$ and $n = m + 1$ give negative
Fibonacci indices; those two values are the separately stated initial values, and the recurrence
is stated for $n \ge m + 2$.

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 15 (`jis-2025-25.1.6-thm-15`).
