# Extended Stirling formula for bishops on a square board

For all natural numbers $m$ and
$k$, the number $B_S(m, k)$ of placements of $k$ nonattacking bishops on the $m \times m$ board
satisfies

$$
B_S(m, k) = \sum_{j=0}^{k} \sum_{i=0}^{j} \binom{\lfloor m/2 \rfloor}{i} S(m - i, m - j)
\sum_{l=0}^{k-j} \binom{\lceil m/2 \rceil}{l} S(m - l, m - k + j),
$$

where $S(a, b)$ is Knuth's extended Stirling number of the second kind for integers $a, b$: the
Stirling number of the second kind when $a, b \ge 0$, the unsigned Stirling number of the first
kind with arguments $-b, -a$ when $a, b < 0$, and $0$ otherwise.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 6 (`jis-2025-25.8.6-thm-6`).
