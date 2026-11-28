# Time derivative of the inverse Cole–Hopf profile

Let $\nu \ne 0$, let $u : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be $C^2$, let $t_0, x_0, t, x \in \mathbb{R}$, and suppose that $u$ solves the viscous Burgers equation $\partial_t u + u\, \partial_x u = \nu\, \partial_x^2 u$ at time $t$ for every $y$. Let the inverse Cole–Hopf profile be

$$\varphi(t, x) = \exp\Big(\int_{t_0}^{t} \Big(\frac{u(s,x_0)^2}{4\nu} - \frac{\partial_x u(s, x_0)}{2}\Big) ds - \frac{1}{2\nu} \int_{x_0}^{x} u(t, y)\, dy\Big)\qquad\text{(oriented integrals)}.$$

Then $s \mapsto \varphi(s, x)$ is differentiable at $t$ with derivative $\Big(\frac{u(t,x)^2}{4\nu} - \frac{\partial_x u(t,x)}{2}\Big)\, \varphi(t, x)$.
