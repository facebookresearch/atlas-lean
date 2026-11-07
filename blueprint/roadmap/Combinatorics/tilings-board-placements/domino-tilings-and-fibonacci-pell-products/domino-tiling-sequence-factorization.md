# Factorization of the domino tiling sequence

Let $d$ and $g$ be sequences of natural
numbers with $d_1 = 1$, $d_2 = 8$, $d_3 = 95$, $d_4 = 1183$ and
$d_{n+4} + 32 d_{n+2} + d_n = 15 d_{n+3} + 15 d_{n+1}$ for all $n \ge 1$, and with $g_1 = 1$,
$g_2 = 4$ and $g_{n+2} + g_n = 5 g_{n+1}$ for all $n \ge 1$. Then $d_n = g_n F_{2n-1}$ for every
$n \ge 1$, where $F_m$ is the $m$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$).

These recurrences determine $d_n$ and $g_n$ for $n \ge 1$: $d_n$ is the number of domino tilings
of $P_5 \times P_{2n-2}$ (OEIS A003775) and $g_n$ is OEIS A004253.

## Sources

- James A. Sellers, "Domino Tilings and Products of Fibonacci and Pell Numbers," Journal of Integer Sequences 5 (2002), Article 02.1.2, second Theorem (`d_n = g_n h_n`), lines 153–154, with `d` defined at lines 146–150 and `g` at line 164, https://cs.uwaterloo.ca/journals/JIS/VOL5/Sellers/sellers4.tex
