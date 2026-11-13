# Recurrence for bishops on white squares

Write $R_W(m, k)$ for the number of placements of
$k$ nonattacking bishops on the white squares (those $(i, j)$ with $i + j$ even) of the
$m \times m$ board $[1, m]^2$, and $\pi(n) \in \lbrace 0, 1 \rbrace$ for the remainder of $n$
modulo $2$. For all natural numbers $m$ and $k$,

$$
R_W(m + 1, k + 1) = R_W(m, k + 1) + \bigl(m - k + \pi(m + 1)\bigr) R_W(m, k),
$$

$R_W(m, 0) = 1$ and $R_W(0, k + 1) = 0$.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`).
