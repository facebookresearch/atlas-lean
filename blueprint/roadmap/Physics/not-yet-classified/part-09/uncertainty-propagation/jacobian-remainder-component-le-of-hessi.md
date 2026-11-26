# Componentwise remainder bound from a Hessian bound

Let $f : \mathbb R^n \to \mathbb R^m$ be differentiable at $x$, and let $U$ be an open set containing the box $[lo, hi]$ on which the component $f_i$ is twice continuously differentiable, with $\lVert D^2 f_i(y)\rVert \le H_i$ for all $y$ in the box (operator norm for the sup norm on $\mathbb R^n$). The other components need no smoothness. If $x$ and $x + \delta$ lie in the box, then

$$\bigl|f_i(x + \delta) - f_i(x) - (Df(x)\,\delta)_i\bigr| \le \frac{H_i}{2}\,\lVert\delta\rVert_\infty^2.$$
