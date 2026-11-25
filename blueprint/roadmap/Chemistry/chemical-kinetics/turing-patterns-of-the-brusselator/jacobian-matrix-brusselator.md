# For a ≠ 0, the Jacobian at the steady state is the Brusselator matrix

For real numbers $a \ne 0$ and $b$, the
[Jacobian matrix](../../../Analysis/real-functions/multivariable-calculus/jacobian-matrix/jacobian-matrix.md)
of the [Brusselator kinetics](brusselator.md) $(f, g)$ at the
[steady state](brusselator-steady-state.md) $(a, b / a)$, whose rows are the partial derivatives
$(f_u, f_v)$ and $(g_u, g_v)$ there, is

$$\begin{pmatrix} b - 1 & a^2 \\ -b & -a^2 \end{pmatrix},$$

the [Brusselator Jacobian](brusselator-jacobian.md). The condition $a \ne 0$ is needed: at $a = 0$
the steady state is $(0, 0)$, where $f_u = -(b + 1)$ differs from $b - 1$ unless $b = 0$.
