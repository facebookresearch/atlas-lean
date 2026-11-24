# P-positions of slow edge Nim on a cube

Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube, where the faces
carrying $A$, $B$, $C$ are opposite those carrying $a$, $b$, $c$. A slow edge move is an edge
move (removing at least one token in total from two faces in different opposite pairs) in which
each face loses at most one token. Let $P$ be the set of positions for which $a + A$, $b + B$
and $c + C$ are all even or all odd. Then no slow edge move leads from a position in $P$ to a
position in $P$, and from every position not in $P$ some slow edge move leads to a position in
$P$.

Since every play terminates, these two properties make $P$ the set of P-positions of the slow
game under normal play.

## Sources

- Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*, INTEGERS 25 (2025), Article G2, Theorem 11.
