# Vertex move on the cube

Label the faces of a cube $f_a, f_b, f_c, f_A, f_B, f_C$, where
$f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and record a position as the tuple
$p = (a, b, c, A, B, C)$ of numbers of tokens on these faces. In the game $C_V$ there is a move
from a position $p$ to a position $q$ when, for some choice of one face from each opposite pair
$\{f_a, f_A\}$, $\{f_b, f_B\}$, $\{f_c, f_C\}$ (three faces that meet at a vertex), $q$ agrees
with $p$ on the other three faces, $q \le p$ on every face, and $q \ne p$; that is, at least one
token in total is removed from the three faces at one vertex.

## Sources

- Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*, INTEGERS 25 (2025), Article G2, Section 1 (the variation `C_V`).
