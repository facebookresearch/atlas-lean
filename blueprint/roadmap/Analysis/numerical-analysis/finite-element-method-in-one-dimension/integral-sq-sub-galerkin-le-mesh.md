# $L^2$ error estimate

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$ with mesh size
$h = \max_i (x_{i+1} - x_i)$, let $u$ be a [classical solution](is-classical-solution.md) of
$-u'' = f$ with $u(0) = u(1) = 0$, and let $c$ be a [solution of the Galerkin
system](is-galerkin-solution.md), with $u_h = p_c$. Then

$$\int_0^1 \big(u(x) - u_h(x)\big)^2\, dx \le \Big(\frac{h}{\pi}\Big)^4 \int_0^1 f(x)^2\, dx,$$

so the $L^2$ error is $O(h^2)$. The proof uses nodal exactness and Wirtinger's inequality on each
element, not the Aubin–Nitsche duality argument.
