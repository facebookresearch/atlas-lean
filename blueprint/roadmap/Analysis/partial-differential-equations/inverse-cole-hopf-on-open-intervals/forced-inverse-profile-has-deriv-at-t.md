# Time derivative of the forced inverse profile on an interval

Let $I, J \subseteq \mathbb{R}$ be open intervals, $\nu \ne 0$, and let $u, F : \mathbb{R}^2 \to \mathbb{R}$ be $C^2$ and $C^1$ on $I \times J$ respectively. Let $t_0, t \in I$ and $x_0, x \in J$, and suppose $u$ solves the forced Burgers equation $\partial_t u + u\, \partial_x u = \nu\, \partial_x^2 u - 2\nu\, \partial_x F$ at time $t$ for every $y \in J$. With the forced inverse profile

$$\varphi(t, x) = \exp\Big(\int_{t_0}^{t} r(s)\, ds - \frac{1}{2\nu} \int_{x_0}^{x} u(t, y)\, dy\Big), \qquad r(s) = \frac{u(s, x_0)^2}{4\nu} - \frac{\partial_x u(s, x_0)}{2} + F(s, x_0),$$

$s \mapsto \varphi(s, x)$ is differentiable at $t$ with derivative $\Big(\frac{u(t,x)^2}{4\nu} - \frac{\partial_x u(t,x)}{2} + F(t, x)\Big) \varphi(t, x)$.
