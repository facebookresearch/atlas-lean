# Floor of greedy mixed bronze sums times $(5 + \sqrt{13})/6$

Let $B_n$ be the bronze
numbers ($B_0 = 0$, $B_1 = 1$, $B_{n+2} = 3B_{n+1} + B_n$, the Lucas sequence $U(3, -1)$), and let
$C_n = B_{n+1} - 2B_n$ and $D_n = B_{n+1} - B_n$ be the companion bronze numbers of the first and
second type. Let $R$ and $R'$ be the integer sequences with $R_{3m} = D_{2m}$,
$R_{3m+1} = 3B_{2m+1}$, $R_{3m+2} = B_{2m+1} + C_{2m+2}$ and $R'_{3m} = D_{2m}$,
$R'_{3m+1} = B_{2m+1}$, $R'_{3m+2} = C_{2m+2}$ for all $m \ge 0$. Let $n$ be a natural number
and $a_0, a_1, a_2, \dots$ natural numbers such that $\sum_{k=0}^{m-1} a_k R_k < R_m$ for every
$m \le n + 1$, and let $t = \sum_{k=0}^{n} a_k R_k$. Then
$\lfloor t (5 + \sqrt{13})/6 \rfloor = \sum_{k=0}^{n} a_k R'_{k+1}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of Theorem 8;
$n$ need not be minimal.

## Sources

- Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 10 (2).
