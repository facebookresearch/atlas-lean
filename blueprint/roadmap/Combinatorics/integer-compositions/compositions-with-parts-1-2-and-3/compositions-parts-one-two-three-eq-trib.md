# Compositions with parts $1$, $2$, $3$ are counted by Tribonacci numbers

Let $T$ be a
sequence of natural numbers with $T_1 = T_2 = 1$, $T_3 = 2$ and
$T_m = T_{m-1} + T_{m-2} + T_{m-3}$ for every $m > 3$. Then for every positive integer $n$, the
number of compositions of $n$ (ordered sequences of positive integers with sum $n$) whose parts
are all $1$, $2$ or $3$ is $T_{n+1}$.

The result is due to V. E. Hoggatt, Jr., and M. Bicknell,
"Palindromic compositions," Fibonacci Quarterly 13 (1975), 350–356,
cited as [V] at source lines 429–430.

Proof: Split each nonempty composition by its first part, sum the resulting recurrence over its
length, and use strong induction, following Stanley, Section 1.2, and OEIS A000073.

## Sources

- Yu-hong Guo, "Some Identities For Palindromic Compositions," Journal of Integer Sequences 21 (2018), Article 18.6.6, Theorem citing [V], lines 118–125, https://cs.uwaterloo.ca/journals/JIS/VOL21/Guo/guo19.tex
