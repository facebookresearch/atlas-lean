# Second spatial derivative of the forced inverse profile

Let $\nu \in \mathbb{R}$, $u, F : \mathbb{R}^2 \to \mathbb{R}$ with $u$ $C^2$, and $t_0, x_0, t, x \in \mathbb{R}$. With the forced inverse profile

$$\varphi(t, x) = \exp\Big(\int_{t_0}^{t} r(s)\, ds - \frac{1}{2\nu} \int_{x_0}^{x} u(t, y)\, dy\Big), \qquad r(s) = \frac{u(s, x_0)^2}{4\nu} - \frac{\partial_x u(s, x_0)}{2} + F(s, x_0),$$

$$\partial_x^2 \varphi(t, x) = \Big(\frac{u(t,x)^2}{4\nu^2} - \frac{\partial_x u(t,x)}{2\nu}\Big) \varphi(t, x),$$

with real division, $a/0 = 0$, so for $\nu = 0$ the right-hand side is $0$.

The displayed formula is to be read with the conventions of the [potential](forced-inverse-potential.md): real division is total, with $a/0 = 0$, so for $\nu = 0$ every term divided by $\nu$ vanishes (not necessarily the whole rate); $\partial_x u(s, x_0)$ is the derivative where $u(s, \cdot)$ is differentiable at $x_0$ and $0$ elsewhere, as for $u(s, y) = |y|$ at $x_0 = 0$; and an oriented integral of a function that is not integrable on the interval is $0$. For arbitrary fields the profile is therefore $\exp$ of the potential as defined, not of a classical expression.

No integrability of the forcing $F(\cdot, x_0)$ along the time path is assumed; the time factor is constant in $x$ and does not affect the spatial derivatives.
