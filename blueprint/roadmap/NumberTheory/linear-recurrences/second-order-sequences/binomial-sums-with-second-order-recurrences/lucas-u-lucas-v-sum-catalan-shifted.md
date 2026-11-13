# Shifted Catalan convolution with Lucas sequences

Let $p$ be an integer, let $U_n$ and
$V_n$ be the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so $U_0 = 0$, $U_1 = 1$, $V_0 = 2$,
$V_1 = p$ and both satisfy $X_{j+2} = p X_{j+1} + X_j$, and let $C_j$ be the $j$-th Catalan
number. Then for all natural numbers $n$ and $m$ with $m \ge 1$, in the rationals,

$$\sum_{k=0}^{n} C_{n-k+m} C_{k+m} U_k V_{n-k} =
2 \binom{2m-1}{m} \frac{(n+m+2)(n+1)}{(n+2m+1)(n+2m+2)} C_{n+m+1} U_n.$$

The paper states $m \in \mathbb{N}_0$; at $m = 0$ the printed right side is twice the sum
($p = 1$, $n = 1$: the sum is $2$, the printed right side is $4$), so $m = 0$ is excluded.

## Sources

- John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.5.
