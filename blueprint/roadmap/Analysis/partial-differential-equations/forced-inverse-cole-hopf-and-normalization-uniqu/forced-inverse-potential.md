# Forced normalized inverse Cole–Hopf potential

For $\nu \in \mathbb{R}$, $u : \mathbb{R}^2 \to \mathbb{R}$, a potential $F : \mathbb{R}^2 \to \mathbb{R}$ and a base point $(t_0, x_0)$, the forced normalized inverse potential is $\psi(t, x) = \int_{t_0}^{t} r(s)\,ds - \frac{1}{2\nu}\int_{x_0}^{x} u(t, y)\,dy$ with $r(s) = \frac{u(s, x_0)^2}{4\nu} - \frac{\partial_x u(s, x_0)}{2} + F(s, x_0)$ (oriented integrals, real division).

Division is total, with $a/0 = 0$ (so for $\nu = 0$ the terms divided by $\nu$ vanish); $\partial_x u(s, x_0)$ is the derivative when $u(s, \cdot)$ is differentiable at $x_0$ and $0$ otherwise; and the oriented integrals are Bochner integrals, taken as $0$ when the integrand is not integrable, so the definition makes sense for arbitrary fields $u$ (and $F$).
