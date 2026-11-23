# Compositions with parts $1$, $2$, $3$ and the Tribonacci sequence

For every positive integer
$n$, the number of compositions of $n$ (ordered sequences of positive integers with sum $n$)
whose parts are all $1$, $2$ or $3$ equals $t_{n+2}$, where $t$ is the Tribonacci sequence
given by $t_0 = t_1 = 0$, $t_2 = 1$ and $t_{k+3} = t_{k+2} + t_{k+1} + t_k$ (OEIS A000073).

This is the case $T_k = t_{k+1}$ of the general statement
[Compositions with parts $1$, $2$, $3$ are counted by Tribonacci numbers](compositions-parts-one-two-three-eq-trib.md):
the sequence $T_k = t_{k+1}$ satisfies $T_1 = T_2 = 1$, $T_3 = 2$ and
$T_m = T_{m-1} + T_{m-2} + T_{m-3}$ for $m > 3$.
