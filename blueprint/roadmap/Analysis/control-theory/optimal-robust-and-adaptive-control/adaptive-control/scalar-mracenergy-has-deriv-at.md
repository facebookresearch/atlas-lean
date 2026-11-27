# Energy derivative for scalar model-reference adaptive control

Let $a, b, \lambda, \gamma, r \in \mathbb{R}$ with $b \ne 0$ and $\gamma > 0$, and let $x, x_m, \hat a : \mathbb{R} \to \mathbb{R}$ and $t \in \mathbb{R}$. Suppose that at $t$ the plant $x' = ax + bu$ runs under the feedback $u = (-\hat a x - \lambda x + r)/b$, the reference model is $x_m' = -\lambda x_m + r$, and the adaptation law is $\hat a' = \gamma\,(x - x_m)\,x$, each as a derivative at $t$. Then the energy

$$V = \tfrac12\Big((x - x_m)^2 + \frac{(a - \hat a)^2}{\gamma}\Big)$$

has derivative $V'(t) = -\lambda\,(x(t) - x_m(t))^2$ at $t$.
