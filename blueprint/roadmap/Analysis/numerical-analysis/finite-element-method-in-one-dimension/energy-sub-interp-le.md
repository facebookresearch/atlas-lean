# Interpolation estimate

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$ with mesh size
$h = \max_i (x_{i+1} - x_i)$, and let $u$ be $C^2$ on $\mathbb{R}$ with [nodal
interpolant](interp.md) $I_h u$. Then

$$a(u - I_h u, u - I_h u) \le \Big(\frac{h}{\pi}\Big)^2 \int_0^1 u''(x)^2\, dx .$$
