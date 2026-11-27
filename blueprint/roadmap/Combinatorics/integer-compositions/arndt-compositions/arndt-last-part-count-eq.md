# Closed formula for Arndt compositions by last part

Let $F_r$ be the $r$-th Fibonacci
number ($F_0 = 0$, $F_1 = 1$) and $b(n, m)$ the number of Arndt compositions of $n$ with last
part $m$. Define $t_1, t_2 : \mathbb{N} \to \mathbb{N}$ by $t_1(0) = 1$, $t_1(1) = 0$,
$t_1(r) = F_{r-2}$ and $t_2(0) = 0$, $t_2(1) = 1$, $t_2(r) = F_{r-1}$ for $r \ge 2$. Then for all
integers $n \ge 1$ and $m \ge 1$: $b(n, m) = 0$ if $n < m$, $b(n, m) = t_1(n - m)$ if
$m \le n < 2m$, and $b(n, m) = t_1(n - m) + t_2(n - 2m)$ if $n \ge 2m$.

The paper leaves the range of $m$ implicit; at $m = 0$ the printed formula fails ($b(1, 0) = 0$,
while the formula gives $t_1(1) + t_2(1) = 1$), so $m \ge 1$ is assumed.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Theorem 9.
