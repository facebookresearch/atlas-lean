# Triple convolution of the Fibonacci 2-, 3- and 5-step numbers

Let $F_j$, $T_j$ and $P_j$
be the Fibonacci $2$-, $3$- and $5$-step numbers, where the Fibonacci $k$-step numbers start
$0, 1$ and each later term is the sum of the $k$ terms before it (terms of negative index being
$0$). For every natural number $n \ge 5$,

$$2 \sum_{k_1 + k_2 + k_3 = n - 5} F_{k_1} T_{k_2} P_{k_3} =
P_n - P_{n-1} + P_{n-2} - T_n - T_{n-2} + F_{n-1},$$

where the sum runs over all triples $(k_1, k_2, k_3)$ of natural numbers with
$k_1 + k_2 + k_3 = n - 5$.

The paper prints this identity with a factor $\tfrac{1}{2}$.

## Sources

- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Theorem 29.
