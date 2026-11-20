# Galerkin orthogonality

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$, let $u$ be a [classical
solution](is-classical-solution.md) of $-u'' = f$ with $u(0) = u(1) = 0$, and let $c$ be a
[solution of the Galerkin system](is-galerkin-solution.md), with $u_h = p_c$. Then
$a(u - u_h, v) = 0$ for every $v$ in the [P1 space](p1-space.md) $V_h$.
