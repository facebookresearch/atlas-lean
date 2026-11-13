# Recurrence for the shifted self-convolution of higher-order Fibonacci numbers

Let
$m \ge 1$ and let $(F_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers with
$F_n = F_{n-1} + \dots + F_{n-m}$ for every integer $n$, $F_i = 0$ for $0 \le i < m - 1$ and
$F_{m-1} = 1$, and for $n \ge 0$ let $w_n = \sum_{j=0}^{n} F_{j+m-1} F_{n-j+m-1}$. Then for
every integer $n \ge 0$, $(m+1) w_{n+1} - 2m w_n = (n+m+2) F_{n+m} - (n+m) F_{n+m-1}$.

## Sources

- Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles and Self-Convolutions of Higher-Order Fibonacci Numbers", Theorem 1.
