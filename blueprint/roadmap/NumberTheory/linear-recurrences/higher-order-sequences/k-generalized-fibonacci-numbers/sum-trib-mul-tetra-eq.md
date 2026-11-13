# Convolution of the Fibonacci 3-step and 4-step numbers as a sum weighted by powers of 2

Let $T_j$ and $Q_j$ be the Fibonacci $3$-step and $4$-step numbers, where the Fibonacci $k$-step
numbers start $0, 1$ and each later term is the sum of the $k$ terms before it (terms of negative
index being $0$). For every natural number $n$,

$$\sum_{j=0}^{n+2} T_j \, Q_{n+2-j} = \sum_{j=0}^{n} 2^j \bigl(T_{n+1-j} - Q_{n-j}\bigr).$$

This is the case $m = 4$ of the paper's Theorem 12 with $n$ replaced by $n + 2$. The paper prints
$Q_{n-j}$ in place of $Q_{n+2-j}$ on the left; as printed, the identity fails at $n = 0$, where
the left side is $0$ and the right side is $1$.

## Sources

- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Corollary 13.
