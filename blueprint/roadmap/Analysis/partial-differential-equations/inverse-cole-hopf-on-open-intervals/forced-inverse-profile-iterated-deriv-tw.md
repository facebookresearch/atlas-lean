# Second spatial derivative of the forced inverse profile on an interval

Let $I, J \subseteq \mathbb{R}$ be open with $J$ an interval, $\nu \in \mathbb{R}$, $u, F : \mathbb{R}^2 \to \mathbb{R}$ with $u$ $C^2$ on $I \times J$, and $t_0, x_0, t, x$ with $x_0, x \in J$ and $t \in I$. With the forced inverse profile

$$\varphi(t, x) = \exp\Big(\int_{t_0}^{t} r(s)\, ds - \frac{1}{2\nu} \int_{x_0}^{x} u(t, y)\, dy\Big), \qquad r(s) = \frac{u(s, x_0)^2}{4\nu} - \frac{\partial_x u(s, x_0)}{2} + F(s, x_0)$$,

$$\partial_x^2 \varphi(t, x) = \Big(\frac{u(t,x)^2}{4\nu^2} - \frac{\partial_x u(t,x)}{2\nu}\Big) \varphi(t, x),$$

with real division (so $\nu = 0$ gives $0$ on the right).
