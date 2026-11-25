# Ref-symmetric squares from the Strachey construction

Let $m$ be a natural number, let
$q = (2m+1)^2$, and let $A_0$, $A_1$ and $M$ be $(2m+1) \times (2m+1)$ arrays of natural
numbers, with rows and columns indexed by $0, 1, \dots, 2m$; write $\bar\imath = 2m - i$ and
$\bar\jmath = 2m - j$. Suppose that every entry of $A_0$ is $0$ or $3$, every row of $A_0$ has
exactly $m+1$ zeros, and the main diagonal and the anti-diagonal of $A_0$ each have exactly
$m+1$ threes; that every entry of $A_1$ is $1$ or $2$, every row of $A_1$ has exactly $m+2$
ones, and the main diagonal and the anti-diagonal of $A_1$ each have exactly $m+2$ ones; that
$A_k(\bar\imath, j) = A_k(i, j)$ and $A_k(m, \bar\jmath) = A_k(m, j)$ for $k = 0, 1$ and all
$i$, $j$; that $M$ is a reduced magic square; and that
$M(i, j) + M(\bar\imath, \bar\jmath) = q - 1$ for all $i$, $j$. Let $B_1(i, j) = M(i, \bar\jmath)$
if $i > m$ and $B_1(i, j) = M(i, j)$ otherwise, and let $B_1^*(i, j) = M(i, \bar\jmath)$ if
$i \ge m$ and $B_1^*(i, j) = M(i, j)$ otherwise. Let $n = 2(2m+1)$ and let $S$ be the square of
order $n$, with rows and columns indexed by $0, 1, \dots, n-1$, made of four
$(2m+1) \times (2m+1)$ blocks whose $(i, j)$ entries are $q A_0(i, j) + B_1(i, j)$ in the top
left block, $q (3 - A_1(i, j)) + B_1(i, \bar\jmath)$ in the top right block,
$q (3 - A_0(i, j)) + B_1^*(i, j)$ in the bottom left block and
$q A_1(i, j) + B_1^*(i, \bar\jmath)$ in the bottom right block. Then $S$ is a reduced magic
square, and $S(i, j) + S(n - 1 - i, j) = n^2 - 1$ for all $i$, $j$.

The last identity is the reduced form of the paper's condition $a_{i,j} + a_{n+1-i,j} = n^2 + 1$.
As in the extended Strachey construction, the statement is vacuous at $m = 0$, where no array
$A_1$ satisfies the row condition.

## Sources

- Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*, Journal of Integer Sequences 27 (2024), Article 24.1.4, Theorem 2, with Definitions 4-6 (`jis-2024-24.1.4-thm-2`).
