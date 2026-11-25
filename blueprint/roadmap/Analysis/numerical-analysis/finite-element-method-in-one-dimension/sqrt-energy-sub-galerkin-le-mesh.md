# Energy error estimate for the P1 Galerkin solution

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$ with mesh size
$h = \max_i (x_{i+1} - x_i)$, let $u$ be a [classical solution](is-classical-solution.md) of
$-u'' = f$ with $u(0) = u(1) = 0$, and let $c$ be a [solution of the Galerkin
system](is-galerkin-solution.md), with $u_h = p_c$. Then

$$\sqrt{a(u - u_h, u - u_h)} \le \frac{h}{\pi} \Big(\int_0^1 f(x)^2\, dx\Big)^{1/2} .$$
