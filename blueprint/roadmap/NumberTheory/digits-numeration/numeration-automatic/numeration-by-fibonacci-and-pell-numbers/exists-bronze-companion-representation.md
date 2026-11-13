# Numeration by bronze and companion bronze numbers

Let $B_n$ be the bronze numbers
($B_0 = 0$, $B_1 = 1$, $B_{n+2} = 3B_{n+1} + B_n$, the Lucas sequence $U(3, -1)$), and let
$C_n = B_{n+1} - 2B_n$ and $D_n = B_{n+1} - B_n$ be the companion bronze numbers of the first and
second type. Let $R$ be the integer sequence with $R_{3m+1} = B_{2m+1}$, $R_{3m+2} = C_{2m+2}$
and $R_{3m} = D_{2m}$ for all $m \ge 0$. Then for every positive integer $t$ there are a natural
number $n \ge 1$ and natural numbers $a_0, a_1, a_2, \dots$ such that $R_n \le t < R_{n+1}$,
$t = \sum_{k=1}^{n} a_k R_k$, $a_k = 0$ for every $k > n$, and: (3) $a_1 \le 3$, and
$a_2 = a_3 = 0$ if $a_1 = 3$; (4) for every $k > 1$, $a_k \le 4$ if $k \equiv 1 \pmod 3$ and
$a_k \le 1$ otherwise; (5) for every $k$ with $a_k = 4$, $a_{k-1} = a_{k+1} = 0$, $a_{k-3} < 4$
and $a_{k+3} < 4$, where an index below $0$ is read as $0$.

The paper's conditions (6) and (7) are omitted: no representation of $50$ satisfies (6)
together with (2)–(5), and the greedy representation $410 = 3B_5 + D_4 + D_2$
($327 + 76 + 7$; digits $a_7 = 3$, $a_6 = 1$, $a_3 = 1$) violates (7).

## Sources

- Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 9 (1)–(5).
