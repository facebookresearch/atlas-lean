# Spatial derivative of the forced inverse profile

Let $\nu \in \mathbb{R}$, $u, F : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$, $t_0, x_0, t \in \mathbb{R}$, and let the forced inverse profile be

$$\varphi(t, x) = \exp\Big(\int_{t_0}^{t} r(s)\, ds - \frac{1}{2\nu} \int_{x_0}^{x} u(t, y)\, dy\Big), \qquad r(s) = \frac{u(s, x_0)^2}{4\nu} - \frac{\partial_x u(s, x_0)}{2} + F(s, x_0)$$ (oriented integrals). If $u(t, \cdot)$ is continuous, then for every $x$ the function $\varphi(t, \cdot)$ is differentiable at $x$ with

$$\partial_x \varphi(t,x) = -\frac{u(t,x)}{2\nu}\, \varphi(t,x).$$

Division by $2\nu$ is real division, so for $\nu = 0$ both sides vanish.
