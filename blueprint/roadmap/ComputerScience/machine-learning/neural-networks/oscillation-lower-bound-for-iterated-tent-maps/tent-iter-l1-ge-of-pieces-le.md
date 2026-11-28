# Functions with few pieces cannot approximate deep tent iterates

Let $\Delta$ be the tent map on $[0, 1]$ and $\Delta^{k}$ its $k$-fold iterate. For every integer $L \ge 2$ and every continuous function $g : \mathbb{R} \to \mathbb{R}$ that is [piecewise affine with at most $n \le 2^{L^2}$ pieces](../piece-count-bounds-for-univariate-relu-networks/pieces-le.md),

$$\int_0^1 \bigl| \Delta^{L^2 + 2}(x) - g(x) \bigr|\, dx \ge \frac{1}{32}.$$
