# Recurrence for bishops on the black squares

Let $R_K(m, k)$ be the number of
nonattacking placements of $k$ bishops on the black squares $(i, j)$, with $i + j$ odd, of the
board $\{1, \dots, m\}^2$, and let $\pi(m) \in \{0, 1\}$ be the remainder of $m$ modulo $2$.
For $m, k \ge 1$,

$$R_K(m, k) = R_K(m-1, k) + (m - k + 1 - \pi(m)) \, R_K(m-1, k-1)$$

in the integers, and for every natural number $m$, $R_K(m, 0) = 1$ and $R_K(0, k) = 0$ for
$k \ge 1$.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`).
