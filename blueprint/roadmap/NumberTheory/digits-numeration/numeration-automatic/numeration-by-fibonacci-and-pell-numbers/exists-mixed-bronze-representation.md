# Mixed bronze numeration

Let $B_n$ be the bronze numbers ($B_0 = 0$, $B_1 = 1$,
$B_{n+2} = 3B_{n+1} + B_n$, the Lucas sequence $U(3, -1)$), and let $C_n = B_{n+1} - 2B_n$ and
$D_n = B_{n+1} - B_n$ be the companion bronze numbers of the first and second type. Let $R$ be
the integer sequence with $R_{3m} = D_{2m}$, $R_{3m+1} = 3B_{2m+1}$ and
$R_{3m+2} = B_{2m+1} + C_{2m+2}$ for all $m \ge 0$. Then for every positive integer $t$ there are
a natural number $n$ and natural numbers $a_0, a_1, a_2, \dots$ such that $R_n \le t < R_{n+1}$,
$t = \sum_{k=0}^{n} a_k R_k$, $a_k = 0$ for every $k > n$, and: (3) $a_0 \le 2$, and
$a_0 \le 1$ if $a_1 = 1$ or $a_2 = 1$; (4) for every $k > 0$, $a_k \le 4$ if $3 \mid k$ and
$a_k \le 1$ otherwise; (5) for every $k$ with $a_k = 4$, $a_{k-1} = a_{k+1} = 0$,
$a_{k-3} < 4$ and $a_{k+3} < 4$; (6) for every $m \ge 0$, if $a_{3m+1} = 1$ then
$a_{3m+2} = 0$, and if $a_{3m+2} = 1$ then $a_{3m+1} = 0$; (7) for every $m \ge 1$ with
$a_{3m} = 3$, if $a_{3m+1} = 1$ or $a_{3m+2} = 1$ then $a_{3m-1} = a_{3m-2} = 0$, and if
$a_{3m-1} = 1$ or $a_{3m-2} = 1$ then $a_{3m+1} = a_{3m+2} = 0$.

## Sources

- Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 8.
