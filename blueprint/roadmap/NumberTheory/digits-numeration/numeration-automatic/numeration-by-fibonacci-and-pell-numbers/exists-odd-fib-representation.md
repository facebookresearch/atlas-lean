# Numeration by odd-indexed Fibonacci numbers

Let $F_n$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$). For every positive integer $t$ there are a
natural number $n$ and natural numbers $a_0, a_1, a_2, \dots$ such that
$F_{2n+1} \le t < F_{2n+3}$, $t = \sum_{k=0}^{n} a_k F_{2k+1}$, $a_0 \le 1$, $a_k \le 2$ for
every $k \ge 1$, $a_1 = 2$ and $a_0 = 1$ do not both hold, and for no $k$ do $a_{k+1} = 2$ and
$a_k = 2$ both hold.

Here $a_k$ is the coefficient the paper calls $a_{2k+1}$; the last two conditions exclude the
digit patterns $2F_3 + F_1$ and $2F_{2k+3} + 2F_{2k+1}$.

## Sources

- Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 1.
