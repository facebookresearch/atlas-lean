# Recurrence for anassas below the diagonal

Let $A(m, k, p)$ be the number of
nonattacking placements of $k$ anassas on the square board $\{1, \dots, m\}^2$ with exactly $p$
of them strictly below the main diagonal, let ${n \brace j}$ be Knuth's extended Stirling
numbers of the second kind, and let $\delta$ be the Kronecker delta. For $m \ge 1$, $k \ge 2$
and $p \ge 1$,

$$A(m, k, p) = A(m-1, k, p) + (m-k+1) A(m-1, k-1, p) + (m-p) A(m-1, k-1, p-1) +
(m-p)(m-k+1) A(m-1, k-2, p-1)$$

in the integers. Moreover, for all natural numbers $m$, $k$ and $p$,
$A(0, k, p) = \delta_{k0} \delta_{p0}$, $A(m, 0, p) = \delta_{p0}$,
$A(m, 1, p) = {m+1 \brace m} \delta_{p0} + {m \brace m-1} \delta_{p1}$ and
$A(m, k, 0) = {m+1 \brace m-k+1}$.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 11 (`jis-2025-25.8.6-thm-11`).
