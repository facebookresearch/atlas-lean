# Extended Strachey construction

Let $m$ be a natural number, let $q = (2m+1)^2$, and let
$A_0$, $A_1$, $B_1$, $B_2$ be $(2m+1) \times (2m+1)$ arrays of natural numbers. Suppose that every
entry of $A_0$ is $0$ or $3$, every row of $A_0$ has exactly $m+1$ zeros, and the main diagonal
and the anti-diagonal of $A_0$ each have exactly $m+1$ threes; that every entry of $A_1$ is $1$
or $2$, every row of $A_1$ has exactly $m+2$ ones, and the main diagonal and the anti-diagonal
of $A_1$ each have exactly $m+2$ ones; and that $B_1$ and $B_2$ are reduced magic squares. Then
the square of order $2(2m+1)$ made of four $(2m+1) \times (2m+1)$ blocks, whose $(i, j)$ entries
are $q A_0(i,j) + B_1(i,j)$ in the top left block, $q (3 - A_1(i,j)) + B_2(i,j)$ in the top
right block, $q (3 - A_0(i,j)) + B_1(i,j)$ in the bottom left block and
$q A_1(i,j) + B_2(i,j)$ in the bottom right block, is a reduced magic square.

At $m = 0$ no array $A_1$ satisfies the row condition (a row of length $1$ cannot hold two
ones), so the statement is vacuous there.

## Sources

- Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*, Journal of Integer Sequences 27 (2024), Article 24.1.4, Theorem 1, with Definitions 1-3 (`jis-2024-24.1.4-thm-1`).
