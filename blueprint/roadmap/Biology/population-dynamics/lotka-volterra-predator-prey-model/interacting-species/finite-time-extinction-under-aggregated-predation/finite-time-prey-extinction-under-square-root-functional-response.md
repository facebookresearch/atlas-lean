# Finite-time prey extinction under a square-root functional response

**Model.** With prey herd behaviour modelled by a square-root functional response, the scaled predator–prey system is

$$
\dot x = r x(1-x) - y\sqrt{x},\qquad \dot y = -\alpha y + \beta y\sqrt{x},\qquad x,y\ge 0,
$$

with $r,\alpha,\beta>0$. The nonnegative equilibria are $P_0 = (0,0)$, $P_1 = (1,0)$ and, for $\alpha<\beta$, the interior point $P_2 = (x^*,y^*)$ with $x^* = (\alpha/\beta)^2$, $y^* = r\alpha(\beta^2-\alpha^2)/\beta^3$. The right-hand side is not differentiable at $x=0$, so the axis $\{x=0\}$ is not covered by standard linearization. $P_2$ is locally asymptotically stable iff $\alpha/\beta > 1/\sqrt3$.

**Theorem (finite-time extinction of prey).** Let $x(0)\in(0,1]$ and $y(0)>0$ satisfy

$$
(r+2\alpha)\sqrt{x(0)} < y(0).
$$

Then $x(t)$ reaches $0$ at a finite time. In particular, for every parameter choice there are positive initial conditions whose trajectories hit the predator axis in finite time, so $P_2$ is never globally asymptotically stable on the open quadrant, even when $\alpha/\beta>1/\sqrt3$ makes it locally stable. This corrects an earlier claim of global stability under that condition.

## Proof sketch

From $\dot y \ge -\alpha y$, $y(t)\ge y(0)e^{-\alpha t}$, and comparison with the logistic equation gives $x(t)\le 1$ when $x(0)\le 1$. While $x>0$, $u = \sqrt x$ satisfies $\dot u = \frac{\dot x}{2\sqrt x} \le \tfrac12 r u - \tfrac12 y(0)e^{-\alpha t}$. Multiplying by the integrating factor $e^{-rt/2}$ and integrating,

$$
\sqrt{x(t)}\,e^{-rt/2} \le \sqrt{x(0)} - \frac{y(0)}{r+2\alpha}\big(1 - e^{-(r/2+\alpha)t}\big),
$$

whose right-hand side becomes negative at a finite time under the stated inequality, so $x$ must hit $0$ before then. The sublinear response $y\sqrt x$ dominates the linear growth $rx$ near $x=0$, which is the mechanism. Numerically, a separatrix (stable manifold of a saddle) divides initial conditions converging to $P_2$ from those going extinct in finite time; $y = (r+2\alpha)\sqrt x$ is an explicit curve lying above it.

## Sources

- Kendall H. Bearden and Kwadwo Antwi-Fordjour, "On a Predator-Prey Model with Square Root Functional Response", *Journal of Applied Nonlinear Dynamics* 15 (2026), 401–408, <https://doi.org/10.5890/jand.2026.06.011>. Preprint version: arXiv:2307.06793 (2023), Section 2 (Theorems 2.1–2.2 recalling the original claims, Theorem 2.3 with its proof, Example 2.1, Remark 2.1), <https://doi.org/10.48550/arXiv.2307.06793>.
