# Spatial derivative of the forced inverse profile on an interval

Let $J \subseteq \mathbb{R}$ be an open interval, $\nu \in \mathbb{R}$, $u, F : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$, $t_0, x_0, t \in \mathbb{R}$, and let the forced inverse profile be

$$\varphi(t, x) = \exp\Big(\int_{t_0}^{t} r(s)\, ds - \frac{1}{2\nu} \int_{x_0}^{x} u(t, y)\, dy\Big), \qquad r(s) = \frac{u(s, x_0)^2}{4\nu} - \frac{\partial_x u(s, x_0)}{2} + F(s, x_0)\qquad\text{(oriented integrals)}.$$

If $x_0, x \in J$ and $u(t, \cdot)$ is continuous on $J$, then $\varphi(t, \cdot)$ is differentiable at $x$ with

$$\partial_x \varphi(t,x) = -\frac{u(t,x)}{2\nu}\, \varphi(t,x).$$

Division by $2\nu$ is real division, so for $\nu = 0$ both sides vanish.

The displayed formula is to be read with the conventions of the [potential](../forced-inverse-cole-hopf-and-normalization-uniqu/forced-inverse-potential.md): real division is total, with $a/0 = 0$, so for $\nu = 0$ every term divided by $\nu$ vanishes (not necessarily the whole rate); $\partial_x u(s, x_0)$ is the derivative where $u(s, \cdot)$ is differentiable at $x_0$ and $0$ elsewhere, as for $u(s, y) = |y|$ at $x_0 = 0$; and an oriented integral of a function that is not integrable on the interval is $0$. For arbitrary fields the profile is therefore $\exp$ of the potential as defined, not of a classical expression.

Only the slice $u(t, \cdot)$ is assumed continuous: nothing makes the normalization rate classical or the time integral finite, and the time factor is whatever the potential's conventions give; it is a constant in $x$, so it does not affect the spatial derivative.
