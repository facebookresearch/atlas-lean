# Rotation move on the cube

Label the faces of a cube $f_a, f_b, f_c, f_A, f_B, f_C$, where
$f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and record a position as the tuple
$p = (a, b, c, A, B, C)$ of numbers of tokens on these faces. A rotation is one of the three
belts of four faces $\{f_a, f_b, f_A, f_B\}$, $\{f_a, f_c, f_A, f_C\}$ and
$\{f_b, f_c, f_B, f_C\}$. In the game $C_R$ there is a move from a position $p$ to a position $q$
when, for some rotation, $q$ agrees with $p$ on the two faces outside the rotation, $q \le p$ on
every face, and $q \ne p$; that is, at least one token in total is removed from the four faces
of the rotation.

## Sources

- Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*, INTEGERS 25 (2025), Article G2, Section 2 (the variation `C_R`).
