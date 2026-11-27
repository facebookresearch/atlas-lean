# Element-wise energy of a function minus a P1 function

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$, let $u$ be $C^2$ on $\mathbb{R}$ and
$d \in \mathbb{R}^{n+1}$, with $p_d$ the [P1 function](p1.md) and $s_i(d)$ the [element
slopes](element-slope.md). Then

$$a(u - p_d, u - p_d) = \sum_{i=0}^{n-1} \int_{x_i}^{x_{i+1}} \big(u'(x) - s_i(d)\big)^2\, dx .$$
