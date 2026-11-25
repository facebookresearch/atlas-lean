# Delayed-average approximation of a progressive process

Let $H$ be a progressive process for a filtration $F$, $M \in \mathbb{R}$, $t \ge 0$ and $n \in \mathbb{N}$, and put
$t_k = kt/(n+1)$. The delayed-average approximation is the [elementary integrand](elementary-integrand.md)
with the $n + 1$ intervals $(t_k, t_{k+1}]$, whose coefficient on $(t_k, t_{k+1}]$ is $0$ for $k = 0$ and,
for $k \ge 1$,

$$\frac{1}{t_k - t_{k-1}} \int_{t_{k-1}}^{t_k} \tau_M(H_s)\, ds$$

(read as $0$ if the interval is degenerate or the integrand not integrable), where
$\tau_M(x) = x\, \mathbf 1_{(-M, M]}(x)$ is the truncation at level $M$. For $M \le 0$ the truncation, hence the
approximation, is $0$.
