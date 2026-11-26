# The settling error never exceeds the initial mismatch

Let $\tau > 0$ and $u$ be real numbers, let $t_0 < t_1$, and let
$y \colon \mathbb{R} \to \mathbb{R}$ be continuous on $[t_0, t_1]$ and differentiable at every
$s \in (t_0, t_1)$ with $\tau\, y'(s) = u - y(s)$ (a first-order stage driven by the held level
$u$). Then $|y(t) - u| \le |y(t_0) - u|$ for every $t \in [t_0, t_1]$, since the factor
$e^{-(t - t_0)/\tau}$ is at most $1$ for $t \ge t_0$ and $\tau > 0$.
