# Arndt compositions with last part at most or at least $k$

Let $F_n$ be the $n$-th
Fibonacci number ($F_0 = 0$, $F_1 = 1$) and $b(n, j)$ the number of Arndt compositions of $n$
with last part $j$. For all integers $k \ge 1$ and $n \ge 2k + 2$, the number of Arndt
compositions of $n$ with last part at most $k$ is
$\sum_{j=1}^{k} b(n, j) = F_n - F_{n-k-1} - F_{n-2k-2}$, and the number with last part at least
$k$ is $\sum_{j=k}^{n} b(n, j) = F_{n-k} + F_{n-2k}$.

The paper prints the second count as $F_{n-k} - F_{n-2k}$, which is false: for $k = 1$ and
$n = 4$ all $F_4 = 3$ Arndt compositions of $4$ have last part at least $1$, while
$F_3 - F_2 = 1$. The sign $+$ is the one the paper's own consequence uses ($F_{n-2} + F_{n-4}$
compositions with last part greater than $1$), and it is what subtracting the number with last
part at most $k - 1$ from $F_n$ gives.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Corollary 4 (`integers-2024-A35-cor-4`).
