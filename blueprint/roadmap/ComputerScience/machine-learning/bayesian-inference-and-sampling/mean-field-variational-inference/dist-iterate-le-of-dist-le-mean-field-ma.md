# Error of an approximate mean-field iteration

Let $\iota$ be finite, $U$ a linear map of $\mathbb{R}^\iota$ with $\lVert U \rVert \le a < 1$ for
the Euclidean operator norm, $h \in \mathbb{R}^\iota$, and let $m$ be a fixed point of the
[mean-field map](mean-field-map.md) $T^\star(x) = \tanh(U x + h)$. If $T$ maps a set $C$
containing $m$ and $x_0$ into itself and $\lVert T x - T^\star x \rVert \le \zeta$ for every
$x \in C$, then for every $k \in \mathbb{N}$,

$$\lVert T^k x_0 - m \rVert \le a^k \lVert x_0 - m \rVert + \zeta\, \frac{1 - a^k}{1 - a}.$$
