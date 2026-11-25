# Spatial derivative of the inverse Cole–Hopf profile

Let $\nu \in \mathbb{R}$, $u : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ and $t_0, x_0, t \in \mathbb{R}$ with $u(t, \cdot)$ continuous, and let the inverse Cole–Hopf profile be

$$\varphi(t, x) = \exp\Big(\int_{t_0}^{t} \Big(\frac{u(s,x_0)^2}{4\nu} - \frac{\partial_x u(s, x_0)}{2}\Big) ds - \frac{1}{2\nu} \int_{x_0}^{x} u(t, y)\, dy\Big)$$. For every $x$, $\varphi(t, \cdot)$ is differentiable at $x$ with $\partial_x \varphi(t, x) = -\frac{u(t,x)}{2\nu}\, \varphi(t, x)$. Division by $2\nu$ is real division, so for $\nu = 0$ both sides vanish.
