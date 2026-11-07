# P-positions of Wythoff's game when positions of total at most 2 are terminal

In the game
$K^2$ on two piles, a move from a position $(x, y)$ with $x + y > 2$ removes a positive number
of tokens from one pile or the same positive number from both piles, and no move is allowed
from a position with $x + y \le 2$. Let $a_n$ be the least integer $m > 2$ that differs from
$a_i$ and $b_i$ for every $i < n$, and let $b_n = a_n + n + 3$, so that $(a_0, b_0) = (3, 6)$.
Let $P$ consist of the positions $(x, y)$ with $x + y \le 2$ together with the pairs
$(a_n, b_n)$ and $(b_n, a_n)$ for $n \ge 0$. Then no move of $K^2$ leads from a position in $P$
to a position in $P$, and from every position not in $P$ some move of $K^2$ leads into $P$.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Proposition 16 (`jis-2026-26.1.6-prop-16`).
