# Unit-step segment bound $H_i$ gives remainder bound $H_i/2$

Let $f : \mathbb{R}^n \to \mathbb{R}^m$ be differentiable at $x \in \mathbb{R}^n$, let
$\delta \in \mathbb{R}^n$, let $i$ be one of the $m$ components and $H_i$ a real number. Suppose
that the segment function of component $i$,

$$\varphi_i(t) = f_i(x + t\,\delta), \qquad t \in \mathbb{R},$$

is twice continuously differentiable on $\mathbb{R}$ with $|\varphi_i''(t)| \le H_i$ for every
$t \in [0, 1]$. Then component $i$ of the [first-order remainder](jacobian-remainder.md)
satisfies

$$\bigl|f_i(x + \delta) - f_i(x) - (Df(x)\,\delta)_i\bigr| \le \frac{H_i}{2} .$$

Only component $i$ needs this smoothness along the segment; the other components enter only
through the differentiability of $f$ at $x$. By the chain rule $\varphi_i'(0) = (Df(x)\,\delta)_i$,
so this is the [scalar Taylor bound](taylor-first-order-bound.md) for $\varphi_i$ on $[0, 1]$ at
$0$ with step $1$. The number $H_i$ bounds $\varphi_i''$, which already carries two factors of
$\delta$: when $f_i$ is twice differentiable,
$\varphi_i''(t) = D^2 f_i(x + t\delta)(\delta, \delta)$. So $H_i$ is a bound along this one
segment, not a bound on the second derivative of $f_i$.
The [scaled segment form](jacobian-remainder-component-le-of-scale.md) and the
[Hessian form](jacobian-remainder-component-le-of-hessi.md) give bounds proportional to
$\|\delta\|^2$.
