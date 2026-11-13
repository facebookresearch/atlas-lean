# Sum formula for bishops on the black squares

Let $R_K(m, k)$ be the number of
nonattacking placements of $k$ bishops on the black squares $(i, j)$, with $i + j$ odd, of the
board $\{1, \dots, m\}^2$, and let ${n \brace j}$ be Knuth's extended Stirling numbers of the
second kind. For all natural numbers $m$ and $k$,

$$R_K(m, k) = \sum_{j=0}^{k} \binom{\lfloor m/2 \rfloor}{j} {m-j \brace m-k}.$$

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`).
