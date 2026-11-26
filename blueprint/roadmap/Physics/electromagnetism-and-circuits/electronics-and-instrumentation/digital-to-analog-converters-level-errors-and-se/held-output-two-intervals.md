# Settling across a change of held level at a junction

Let $\tau > 0$, $u_1$ and $u_2$ be real numbers and $t_0 < t_1 < t_2$, and let
$y \colon \mathbb{R} \to \mathbb{R}$ be continuous on $[t_0, t_2]$ and differentiable at every point
of $(t_0, t_1)$ and of $(t_1, t_2)$, with $\tau\, y' = u_1 - y$ on $(t_0, t_1)$ and
$\tau\, y' = u_2 - y$ on $(t_1, t_2)$. Then for every $t \in [t_1, t_2]$

$$y(t) = u_2 + (y_1 - u_2)\, e^{-(t - t_1)/\tau},$$

where

$$y_1 = u_1 + (y(t_0) - u_1)\, e^{-(t_1 - t_0)/\tau}$$

is the endpoint value of the first interval: the second interval starts from it. Continuity at the
junction $t_1$ is the no-reset hypothesis; no derivative is assumed there.
