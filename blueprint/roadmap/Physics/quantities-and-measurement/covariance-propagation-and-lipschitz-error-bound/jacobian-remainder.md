# First-order remainder $f(x+\delta) - f(x) - Df(x)\,\delta$

For a map $f : \mathbb{R}^n \to \mathbb{R}^m$ and vectors $x, \delta \in \mathbb{R}^n$, the
first-order (Jacobian) remainder is

$$R(x, \delta) = f(x + \delta) - f(x) - Df(x)\,\delta \;\in \mathbb{R}^m,$$

where $Df(x)$ is the derivative (Jacobian matrix) of $f$ at $x$, with the convention that it is
$0$ where $f$ is not differentiable at $x$; there $R(x, \delta) = f(x + \delta) - f(x)$. The
first-order propagation $f(x + \delta) \approx f(x) + Df(x)\,\delta$ is an approximation: the
remainder is not zero in general. For example, for the square map $y \mapsto y^2$ on $\mathbb{R}$
($n = m = 1$), $R(0, \delta) = \delta^2$, which is $1/4$ at $\delta = 1/2$. The componentwise
bounds on $R$ ([segment bound](jacobian-remainder-component-le.md),
[scaled segment bound](jacobian-remainder-component-le-of-scale.md),
[Hessian bound](jacobian-remainder-component-le-of-hessi.md)) all assume that $f$ is
differentiable at $x$.
