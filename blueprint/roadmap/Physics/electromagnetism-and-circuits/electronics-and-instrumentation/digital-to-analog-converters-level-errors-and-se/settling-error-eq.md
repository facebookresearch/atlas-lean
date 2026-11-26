# The settling error is the initial mismatch times $e^{-(t - t_0)/\tau}$

Let $\tau > 0$ and $u$ be real numbers, let $t_0 < t_1$, and let
$y \colon \mathbb{R} \to \mathbb{R}$ be continuous on $[t_0, t_1]$ and differentiable at every
$s \in (t_0, t_1)$ with $\tau\, y'(s) = u - y(s)$ (a first-order stage driven by the held level
$u$). Then for every $t \in [t_0, t_1]$

$$|y(t) - u| = |y(t_0) - u|\, e^{-(t - t_0)/\tau}.$$
