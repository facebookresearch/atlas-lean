# Self-convolution of higher-order Fibonacci numbers

Let $m \ge 1$ and let
$(F_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers with
$F_n = F_{n-1} + \dots + F_{n-m}$ for every integer $n$, $F_i = 0$ for $0 \le i < m - 1$ and
$F_{m-1} = 1$. For $p \ge 0$ let $w_p = \sum_{j=0}^{p} F_{j+m-1} F_{p-j+m-1}$; for integers
$N$, $l$ and rational $q$ let $S(N, l, q) = \sum_{k=0}^{N} q^k F_{k+l}$ and
$S_2(N, l, q) = \sum_{k=0}^{N} k q^k F_{k+l}$, both equal to $0$ when $N < 0$. Put
$q = (m+1)/(2m)$. Then for every integer $n \ge 2m - 2$, writing $p = n - 2m + 2$,

$$
\sum_{i=0}^{n} F_i F_{n-i} = w_p = \left(\frac{2m}{m+1}\right)^{p} +
\frac{(2m)^{p-1}}{(m+1)^{p}} \bigl((m+2) S(p-1, m, q) + S_2(p-1, m, q) -
m S(p-1, m-1, q) - S_2(p-1, m-1, q)\bigr).
$$

The source states the formula for all $n \ge 0$, but for $m \ge 2$ it fails when
$n < 2m - 2$: at $m = 2$ and $n = 0$ the left side is $0$ and the right side is $9/16$.

## Sources

- Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles and Self-Convolutions of Higher-Order Fibonacci Numbers", Theorem 4.
