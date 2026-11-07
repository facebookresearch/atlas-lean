# Arshon's formula for nonattacking bishops (Kotěšovec's form)

For all natural numbers $m$
and $k$, the number $B_S(m, k)$ of placements of $k$ nonattacking bishops on the $m \times m$
board satisfies

$$
B_S(m, k) = \sum_{j=0}^{m} \sum_{i=0}^{\lfloor (m+1)/2 \rfloor}
\binom{\lfloor (m+1)/2 \rfloor}{i} S\bigl(i + \lfloor m/2 \rfloor, m - j\bigr)
\sum_{l=0}^{\lfloor m/2 \rfloor} \binom{\lfloor m/2 \rfloor}{l}
S\bigl(l + \lfloor (m+1)/2 \rfloor, m - k + j\bigr),
$$

where, for integers $a \ge 0$ and $b$, $S(a, b)$ is the Stirling number of the second kind when
$b \ge 0$ and $0$ when $b < 0$ (Knuth's extended Stirling numbers of the second kind).

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 3 (Arshon, Kotěšovec) (`jis-2025-25.8.6-thm-3`).
