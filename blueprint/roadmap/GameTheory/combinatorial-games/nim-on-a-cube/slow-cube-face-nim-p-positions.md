# P-positions of slow face Nim on a cube

Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube. A slow face move is
a face move that removes exactly one token from one face. Let $P$ be the set of positions with
$a + b + c + A + B + C$ even. Then no slow face move leads from a position in $P$ to a position
in $P$, and from every position not in $P$ some slow face move leads to a position in $P$.

Since every play terminates, these two properties make $P$ the set of P-positions of the slow
game under normal play.

## Sources

- Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*, INTEGERS 25 (2025), Article G2, Theorem 12 (`integers-2025-G2-thm-12`).
