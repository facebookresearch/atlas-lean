# Second moment of the weighted quadratic-variation error

Let $B$ be a pre-Brownian motion adapted to a filtration $F$, with increments $B_t - B_s$ ($s \le t$)
independent of $F_s$, and let $\varphi$ be measurable with $|\varphi| \le C$. Then for every $t \ge 0$ and
$n \ge 1$, the [weighted quadratic-variation error](weighted-qverror.md) $E_n$ satisfies

$$\mathbb E\bigl[E_n^2\bigr] = \mathbb E\Bigl[ \Bigl( \sum_{k < n} \varphi(B_{t_k}) \bigl( (\Delta B_k)^2 - \Delta t \bigr) \Bigr)^2 \Bigr] \le \frac{2 C^2 t^2}{n},$$

with $t_k = tk/n$, $\Delta B_k = B_{t_{k+1}} - B_{t_k}$ and $\Delta t = t/n$.
