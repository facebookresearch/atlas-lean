# Scaled segment bound gives remainder bound $H_i\Vert\delta\Vert^2/2$

Let $f : \mathbb{R}^n \to \mathbb{R}^m$ be differentiable at $x \in \mathbb{R}^n$, let
$\delta \in \mathbb{R}^n$, let $i$ be one of the $m$ components and $H_i$ a real number, and write
$\|\delta\| = \max_j |\delta_j|$ for the sup norm. Suppose that the segment function
$\varphi_i(t) = f_i(x + t\,\delta)$ is twice continuously differentiable on $\mathbb{R}$ with

$$|\varphi_i''(t)| \le H_i\, \|\delta\|^2 \qquad \text{for every } t \in [0, 1] .$$

Then component $i$ of the [first-order remainder](jacobian-remainder.md) satisfies

$$\bigl|f_i(x + \delta) - f_i(x) - (Df(x)\,\delta)_i\bigr| \le \frac{H_i}{2}\, \|\delta\|^2 .$$

This is the [unit-step segment bound](jacobian-remainder-component-le.md) with the bound
$H_i \|\delta\|^2$. The hypothesis still bounds the second derivative along the given segment,
not the second derivative of $f_i$; a bound on the latter is the
[Hessian form](jacobian-remainder-component-le-of-hessi.md). With the unscaled hypothesis
$|\varphi_i''| \le H_i$ on $[0, 1]$ the conclusion fails: for the square map $y \mapsto y^2$ on
$\mathbb{R}$ at $x = 0$ with $\delta = 1/2$, $\varphi(t) = t^2/4$ has $\varphi'' = 1/2$, so
$H = 1/2$ satisfies that hypothesis, while the remainder $1/4$ exceeds
$H \|\delta\|^2 / 2 = 1/16$.
