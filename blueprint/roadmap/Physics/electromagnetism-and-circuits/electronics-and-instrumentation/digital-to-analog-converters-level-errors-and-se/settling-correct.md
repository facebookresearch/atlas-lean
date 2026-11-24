# Settling on a holding interval: formula, endpoint value and error law

Let $\tau > 0$ and $u$ be real numbers, let $t_0 < t_1$, and let
$y \colon \mathbb{R} \to \mathbb{R}$ be continuous on $[t_0, t_1]$ and differentiable at every
$s \in (t_0, t_1)$ with $\tau\, y'(s) = u - y(s)$ (a first-order stage driven by the held level
$u$). Then all of the following hold.

- For every $t \in [t_0, t_1]$, $y(t) = u + (y(t_0) - u)\, e^{-(t - t_0)/\tau}$, the
  [settling output](settling-output.md) with initial value $y(t_0)$.
- At the right endpoint, $y(t_1) = u + (y(t_0) - u)\, e^{-(t_1 - t_0)/\tau}$.
- For every $t \in [t_0, t_1]$, $|y(t) - u| = |y(t_0) - u|\, e^{-(t - t_0)/\tau}$.
