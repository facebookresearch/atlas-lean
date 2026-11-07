# Extended Stirling formula for bishops on white squares

For all natural numbers $m$ and
$k$, the number $R_W(m, k)$ of placements of $k$ nonattacking bishops on the white squares (those
$(i, j)$ with $i + j$ even) of the $m \times m$ board $[1, m]^2$ satisfies

$$
R_W(m, k) = \sum_{j=0}^{k} \binom{\lceil m/2 \rceil}{j} S(m - j, m - k),
$$

where $S(a, b)$ is Knuth's extended Stirling number of the second kind for integers $a, b$: the
Stirling number of the second kind when $a, b \ge 0$, the unsigned Stirling number of the first
kind with arguments $-b, -a$ when $a, b < 0$, and $0$ otherwise.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`).
