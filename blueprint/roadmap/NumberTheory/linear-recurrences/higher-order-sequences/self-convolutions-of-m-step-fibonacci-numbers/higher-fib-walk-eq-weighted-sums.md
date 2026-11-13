# Explicit formula for the shifted self-convolution of higher-order Fibonacci numbers

Let
$m \ge 1$ and let $(F_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers with
$F_n = F_{n-1} + \dots + F_{n-m}$ for every integer $n$, $F_i = 0$ for $0 \le i < m - 1$ and
$F_{m-1} = 1$. For $n \ge 0$ let $w_n = \sum_{j=0}^{n} F_{j+m-1} F_{n-j+m-1}$; for integers
$N$, $l$ and rational $q$ let $S(N, l, q) = \sum_{k=0}^{N} q^k F_{k+l}$ and
$S_2(N, l, q) = \sum_{k=0}^{N} k q^k F_{k+l}$, both equal to $0$ when $N < 0$. Put
$q = (m+1)/(2m)$. Then for every integer $n \ge 0$,

$$
w_n = \left(\frac{2m}{m+1}\right)^{n} +
\frac{(2m)^{n-1}}{(m+1)^{n}} \bigl((m+2) S(n-1, m, q) + S_2(n-1, m, q) -
m S(n-1, m-1, q) - S_2(n-1, m-1, q)\bigr).
$$

At $n = 0$ the weighted sums have upper limit $-1$ and are empty.

## Sources

- Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles and Self-Convolutions of Higher-Order Fibonacci Numbers", Theorem 3.
