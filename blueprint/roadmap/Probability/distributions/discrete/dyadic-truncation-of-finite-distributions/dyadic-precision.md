# Dyadic Precision

For $K \in \mathbb{N}$ and $\gamma \in \mathbb{R}$, the dyadic precision is

$$t(K, \gamma) = \min\big\{ m \in \mathbb{N} : N \le 2^m \big\}, \qquad N = \Big\lceil \frac{16 K}{\gamma} \Big\rceil_+,$$

where $\lceil x \rceil_+$ is the natural-number ceiling, equal to $0$ for $x \le 0$, and $x / 0 = 0$. For $\gamma > 0$ and $K \ge 1$ this is $\max\big(0, \lceil \log_2 \lceil 16K/\gamma \rceil \rceil\big)$; it is $0$ whenever $N \le 1$.
