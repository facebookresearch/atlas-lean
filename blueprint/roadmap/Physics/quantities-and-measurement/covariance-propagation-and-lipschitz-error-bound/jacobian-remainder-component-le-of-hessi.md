# Box Hessian bound gives remainder bound $H_i\Vert\delta\Vert^2/2$

Let $f : \mathbb{R}^n \to \mathbb{R}^m$ be differentiable at $x \in \mathbb{R}^n$, let
$\delta \in \mathbb{R}^n$, let $i$ be one of the $m$ components and $H_i$ a real number. Let
$\mathrm{lo}, \mathrm{hi} \in \mathbb{R}^n$ and let $[\mathrm{lo}, \mathrm{hi}]$ be the box of
points $y$ with $\mathrm{lo}_j \le y_j \le \mathrm{hi}_j$ for every $j$. Suppose that the
component $f_i$ is twice continuously differentiable on an open set $U$ containing the box, that
its second derivative satisfies

$$\|D^2 f_i(y)\| \le H_i \qquad \text{for every } y \in [\mathrm{lo}, \mathrm{hi}],$$

the operator norm for the sup norm $\|v\| = \max_j |v_j|$ on $\mathbb{R}^n$, and that $x$ and
$x + \delta$ lie in the box. Then component $i$ of the
[first-order remainder](jacobian-remainder.md) satisfies

$$\bigl|f_i(x + \delta) - f_i(x) - (Df(x)\,\delta)_i\bigr| \le \frac{H_i}{2}\, \|\delta\|^2 .$$

The other components enter only through the differentiability of $f$ at $x$. By the chain rule
$(Df(x)\,\delta)_i = Df_i(x)\,\delta$, so this is the
[first-order remainder bound for a $C^2$ measurement function](../propagation-of-measurement-uncertainty/measurement-function-first-order-remaind-2.md)
applied to $f_i$.
