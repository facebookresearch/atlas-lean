# Misère P-positions of face Nim on a cube

Write positions of the game $C_F$ (Nim with six
heaps) as tuples $p = (a, b, c, A, B, C)$ of numbers of tokens on the faces
$f_a, f_b, f_c, f_A, f_B, f_C$, where $f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and let
$\oplus$ be the Nim-sum (bitwise exclusive or) of natural numbers. Let $\mathcal P$ be any set
of positions such that a position lies in $\mathcal P$ if and only if it has a face move and
every face move from it leads to a position outside $\mathcal P$; this is the set of
P-positions under misère play, where the player making the last move loses. Let $p$ be a
position in which every entry is at most $C$, and $a \le A$, $b \le B$ and $a \le b$. Then
$p \in \mathcal P$ if and only if either $C \ge 2$ and $a \oplus b \oplus c \oplus A \oplus B
\oplus C = 0$, or $C < 2$ and $a \oplus b \oplus c \oplus A \oplus B \oplus C = 1$.

## Sources

- Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*, INTEGERS 25 (2025), Article G2, Theorem 9 (`integers-2025-G2-thm-9`).
