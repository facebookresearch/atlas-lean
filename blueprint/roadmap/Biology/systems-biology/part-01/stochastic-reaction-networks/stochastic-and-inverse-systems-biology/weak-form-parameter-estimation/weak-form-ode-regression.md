# Weak-form linear regression for ODE parameters

Let $u : [0, T] \to \mathbb R^d$ solve $\dot u = \Theta(u)\, W$, where $\Theta(u) = (f_1(u), \dots, f_J(u)) \in \mathbb R^{1 \times J}$ is a row of known feature functions and $W \in \mathbb R^{J \times d}$ the unknown parameters (each equation linear in its parameters). For a test function $\phi \in C^1_c((0, T))$, integration by parts gives the weak form

$$-\int_0^T \dot\phi(t)\, u(t)\, dt = \int_0^T \phi(t)\, \Theta(u(t))\, dt\; W.$$

Given samples $U \in \mathbb R^{(M+1) \times d}$ of $u$ on a uniform grid with step $\Delta t$ and test functions $\phi_1, \dots, \phi_K$, each supported on $[t_k - m_t\Delta t, t_k + m_t\Delta t]$, discretize the integrals by quadrature with matrices $\phi, \dot\phi \in \mathbb R^{K \times (M+1)}$ (rows: the test functions and their derivatives at the grid, times quadrature weights) to obtain the linear system

$$G W \approx B, \qquad G = \phi\, \Theta(U) \in \mathbb R^{K \times J}, \quad B = -\dot\phi\, U \in \mathbb R^{K \times d},$$

with no derivative of the data and no forward ODE solve. The ordinary least-squares problem $\min_W \|GW - B\|_F$ has a unique solution, $\hat W = (G^\top G)^{-1} G^\top B$, if and only if $\operatorname{rank} G = J$; this full column rank of $G$ is assumed directly. The authors' conditions ($\phi_k \in C^p_c$ with $p \ge 1$; $\operatorname{rank}\phi = K$; $\operatorname{rank}\Theta(U) = J$; $J \le K \le M + 1 - 2m_t$) do not imply it, because full rank of the two factors does not give full column rank of their product: with a single nonzero constant feature ($J = 1$) and a single smooth odd test function ($K = 1$) sampled on a grid symmetric about its centre, the quadrature weights are symmetric and $G = 0$.

## Expansion

Multiply the ODE by $\phi$ and integrate; the boundary terms vanish because $\phi$ is compactly supported in the open interval, moving the time derivative from $u$ to $\phi$. The noisy data then appear in $B$ only linearly and in $G$ through $\Theta(U)$, which makes this an errors-in-variables regression rather than a standard least-squares problem: OLS is biased in general, which motivates the [WENDy correction](wendy-errors-in-variables-irls.md). Smooth (e.g. $C^\infty$ bump) test functions reduce the quadrature error.

## Sources

- D. M. Bortz, D. A. Messenger and V. Dukić, "Direct estimation of parameters in ODE models using WENDy: weak-form estimation of nonlinear dynamics", *Bulletin of Mathematical Biology* 85 (2023), <https://doi.org/10.1007/s11538-023-01208-6> (PMC10556152). Section 2, equations (1)–(6), Algorithm 1 and Conditions 1–4.
