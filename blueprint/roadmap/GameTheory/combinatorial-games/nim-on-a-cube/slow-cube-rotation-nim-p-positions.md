# P-positions of slow rotation Nim on a cube

Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube, where the faces
carrying $A$, $B$, $C$ are opposite those carrying $a$, $b$, $c$. A slow rotation move is a
rotation move (removing at least one token in total from the four faces of one rotation, that is
from the faces of two opposite pairs) in which each face loses at most one token. Let $P$ be any
set of positions such that $p \in P$ if and only if no slow rotation move from $p$ leads to a
position in $P$ (the P-positions under normal play). Then for every position $p$ with
$a \le A$, $b \le B$ and $c \le C$, we have $p \in P$ if and only if the vector of remainders
$(a, b, c, A, B, C) \bmod 2$ is one of $(0, 0, 0, 0, 0, 0)$, $(0, 0, 0, 1, 1, 1)$,
$(1, 1, 1, 0, 0, 0)$ and $(1, 1, 1, 1, 1, 1)$.

## Sources

- Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*, INTEGERS 25 (2025), Article G2, Theorem 13.
