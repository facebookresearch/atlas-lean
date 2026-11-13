# Quasi-polynomial formula for bishops on a square board

Write $B_S(m, k)$ for the number of
placements of $k$ nonattacking bishops on the $m \times m$ board $[1, m]^2$,
$\pi(m) \in \lbrace 0, 1 \rbrace$ for the remainder of $m$ modulo $2$, and
$c_{k,d}(z) \in \mathbb{C}$ for the constituent coefficient of the bishop colour quasi-polynomials
(defined for natural $k, d$ and complex $z$). For all natural numbers $m$ and $k$, as complex
numbers,

$$
B_S(m, k) = \sum_{d=0}^{2k} \Biggl( \sum_{j=0}^{k} \sum_{i=0}^{d}
c_{j,i}\bigl(-\pi(m)\bigr)\, c_{k-j,\,d-i}\bigl(\pi(m)\bigr) \Biggr) m^d.
$$

The factors $c_{j,i}(-\pi(m))$ and $c_{k-j,d-i}(\pi(m))$ are the coefficients of the corresponding
quasi-polynomial formulas for bishops on the white and on the black squares.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 10 (`jis-2025-25.8.6-thm-10`).
