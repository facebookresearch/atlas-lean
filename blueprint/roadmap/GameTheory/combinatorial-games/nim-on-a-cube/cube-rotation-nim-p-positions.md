# P-positions of rotation Nim on a cube

Write positions of the game $C_R$ as tuples
$(a, b, c, A, B, C)$ of numbers of tokens on the faces $f_a, f_b, f_c, f_A, f_B, f_C$, where
$f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$. Let $\mathcal P$ be the set of positions with
$a + A = b + B = c + C$. Then no rotation move leads from a position in $\mathcal P$ to a position
in $\mathcal P$, and from every position outside $\mathcal P$ there is a rotation move to a
position in $\mathcal P$.

Every move removes a token, so the game terminates and $\mathcal P$ is exactly the set of
P-positions (second-player wins) under normal play.

## Sources

- Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*, INTEGERS 25 (2025), Article G2, Theorem 5.
