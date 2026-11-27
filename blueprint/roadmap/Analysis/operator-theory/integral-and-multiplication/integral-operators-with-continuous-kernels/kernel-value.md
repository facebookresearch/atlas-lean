# Kernel value

Let $\pi(t) = \max(0, \min(1, t))$ be the projection of $\mathbb{R}$ onto
$[0, 1]$. For a continuous kernel $k$ on $[0, 1] \times [0, 1]$, a function
$f \in C([0, 1], \mathbb{R})$ and a point $x \in [0, 1]$, the kernel value is the real number

$$\int_0^1 k(x, \pi(t))\, f(\pi(t))\, dt.$$

Since $\pi(t) = t$ for $t \in [0, 1]$, it equals $\int_0^1 k(x, t)\, f(t)\, dt$, the value at
$x$ of the integral operator with kernel $k$ applied to $f$.
