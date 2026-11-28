# Centring does not raise the rank

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with
[centred matrix](../principal-component-analysis/center.md)
$X_c = X - \mathbf 1 \bar x^\top$. For every $n$,

$$\operatorname{rank} X_c \le \operatorname{rank} X,$$

since $X_c = (I_n - \frac1n \mathbf 1 \mathbf 1^\top) X$.
