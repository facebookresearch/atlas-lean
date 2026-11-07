# Triple convolution of the Fibonacci 2-, 4- and 5-step numbers

Let $F_j$, $Q_j$ and $P_j$
be the Fibonacci $2$-, $4$- and $5$-step numbers, where the Fibonacci $k$-step numbers start
$0, 1$ and each later term is the sum of the $k$ terms before it (terms of negative index being
$0$). For every natural number $n \ge 5$,

$$2 \sum_{k_1 + k_2 + k_3 = n - 5} F_{k_1} Q_{k_2} P_{k_3}
= -2Q_n - 2Q_{n-2} + P_{n+1} + P_{n-2} - F_{n+1} + 2F_n,$$

where the sum runs over all triples $(k_1, k_2, k_3)$ of natural numbers with
$k_1 + k_2 + k_3 = n - 5$.

The paper prints this identity with a factor $\tfrac{1}{2}$ on part of the right side.

## Sources

- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Theorem 28.
