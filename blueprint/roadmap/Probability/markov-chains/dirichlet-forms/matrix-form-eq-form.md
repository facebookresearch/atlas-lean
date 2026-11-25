# A symmetric matrix form is the form of the generator $-A$

Let $S$ be a finite set and $A$ a real symmetric $S \times S$ matrix. Then for all
$u, v : S \to \mathbb{R}$ the [bilinear form of $A$](matrix-form.md) equals the [form](form.md)
(1.2.27) with $m = 1$ and $Q = -A$:

$$\sum_{x, y} u(x) A(x, y) v(y) = \frac{1}{2} \sum_{x, y} \bigl(-A(x, y)\bigr) \bigl(u(x) - u(y)\bigr)\bigl(v(x) - v(y)\bigr) + \sum_x \Bigl(\sum_y A(x, y)\Bigr) u(x) v(x) .$$
