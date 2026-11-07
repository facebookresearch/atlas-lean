# Recurrence for the subword $U^m$ in non-decreasing Dyck paths

Let $m \ge 1$. Let
$d_w(n)$ be the total number of occurrences of the subword $w$ over all non-decreasing Dyck paths
of semilength $n$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every
$n > m$,

$$d_{U^m}(n) = 3\,d_{U^m}(n-1) - d_{U^m}(n-2) + F_{2(n-m)} + F_{2(n-2)} -
\sum_{k=1}^{m-2} k\,F_{2(n-k-2)}$$

(the sum is empty when $m \le 2$); moreover $d_{U^m}(n) = 0$ for every $n < m$, and
$d_{U^m}(m) = 1$.

The source writes $n \le m$ for the vanishing case, which contradicts $d_{U^m}(m) = 1$; the
vanishing case is stated for $n < m$.

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 13 (`jis-2025-25.1.6-thm-13`).
