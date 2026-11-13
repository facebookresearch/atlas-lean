# Komak's description of the P-positions of $K^2$

Let $\varphi$ be the golden ratio
and $g$ the sequence of Komak et al. Let $S$ be the set of pairs $(x, y)$ of natural numbers
with $x + y \le 2$, together with the pairs
$(\lfloor n\varphi \rfloor + g(n) - 1, \lfloor n\varphi^2 \rfloor + g(n))$ and
$(\lfloor n\varphi^2 \rfloor + g(n), \lfloor n\varphi \rfloor + g(n) - 1)$ for all $n \ge 0$.
In the game $K^2$ (Wythoff's game in which the positions with $x + y \le 2$ are terminal),
no move leads from a position in $S$ to a position in $S$, and from every position outside
$S$ some move leads to a position in $S$.

These two properties determine the set of P-positions, so the P-positions of $K^2$ are
exactly the positions in $S$. The source omits the terminal positions $(0, 0)$ and $(1, 1)$,
which are P-positions since no move leaves them; they are included here.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Theorem 2 (`jis-2026-26.1.6-thm-2`).
