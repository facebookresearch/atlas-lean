# Recurrence for the subword $UD^m$ in non-decreasing Dyck paths

Let $m \ge 1$. Let
$d_w(n)$ be the total number of occurrences of the subword $w$ over all non-decreasing Dyck paths
of semilength $n$, let $l_{n,k}$ be the number of non-decreasing Dyck paths of semilength $n$
whose last peak has height $k$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$).
Then for every $n$ with $n > m$ and $n \ge 3$,

$$d_{UD^m}(n) = 3\,d_{UD^m}(n-1) - d_{UD^m}(n-2) + F_{2(n-m)-1} + l_{n-1,m-1} - l_{n-2,m-1};$$

moreover $d_{UD^m}(n) = 0$ for every $n < m$, and $d_{UD^m}(m) = 1$.

The source states the recurrence for $n \ge m$; $n = m$ is the separately stated initial value,
and the added condition $n \ge 3$ excludes only $(m, n) = (1, 2)$, where $d_{UD}(2) = 3$ but the
right side is $3 \cdot 1 - 0 + F_1 + l_{1,0} - l_{0,0} = 4$ (the empty path has no peak).

## Sources

- Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16 (`jis-2025-25.1.6-thm-16`).
