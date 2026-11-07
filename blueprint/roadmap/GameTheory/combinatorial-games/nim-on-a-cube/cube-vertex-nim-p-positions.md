# P-positions of vertex Nim on a cube

Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube, where the faces
carrying $A$, $B$, $C$ are opposite those carrying $a$, $b$, $c$; a vertex move removes at
least one token in total from the three faces at one vertex (one face from each opposite pair).
Let $P$ be the set of positions with $a = A$, $b = B$ and $c = C$. Then no vertex move leads
from a position in $P$ to a position in $P$, and from every position not in $P$ some vertex
move leads to a position in $P$.

Since every play terminates, these two properties make $P$ the set of P-positions
(second-player wins) under normal play.

## Sources

- Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*, INTEGERS 25 (2025), Article G2, Theorem 2 (`integers-2025-G2-thm-2`).
