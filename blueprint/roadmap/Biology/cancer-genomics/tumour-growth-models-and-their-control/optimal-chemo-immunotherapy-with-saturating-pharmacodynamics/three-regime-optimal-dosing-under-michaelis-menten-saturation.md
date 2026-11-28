# Three-regime optimal dosing under Michaelis–Menten saturation in chemo-immunotherapy

Consider tumor burden $x$, immune effector density $y$ and tumor-associated antigen $z$, under chemotherapy $u \in [0, u_{\max}]$ and immunotherapy $v \in [0, v_{\max}]$ acting through saturating (Michaelis–Menten/$E_{\max}$) maps:

$$
\begin{aligned}
\dot x &= \xi x\Big(1 - \frac{x}{x_\infty}\Big) - \theta x y - \frac{\alpha x u}{1 + u}, \\
\dot y &= a(1 - bx) y z + \gamma - \delta y - \frac{\kappa y u}{1 + u} + \frac{\nu y v}{1 + v}, \\
\dot z &= \sigma x + \frac{\psi x u}{1 + u} - \mu z .
\end{aligned}
$$

The cost has a running state term $\ell$ and linear exposure penalties, $L = \ell(x, y, z) + A u + B v$ with $A, B > 0$. With costates $\lambda$, the Hamiltonian is

$$
H = \ell + A u + B v + \Phi_u(t)\frac{u}{1+u} + \Phi_v(t)\frac{v}{1+v} + (\text{control-free terms}),
$$

where $\Phi_u = -\alpha x\lambda_x - \kappa y\lambda_y + \psi x\lambda_z$ and $\Phi_v = \nu y\lambda_y$ are the switching potentials.

**Proposition (pointwise minimizers).** For fixed $t$, the Hamiltonian minimizer in the chemotherapy channel is

$$
u^*(t) = \begin{cases} 0, & \Phi_u(t) \ge -A, \\ -1 + \sqrt{-\Phi_u(t)/A}, & -A(1 + u_{\max})^2 < \Phi_u(t) < -A, \\ u_{\max}, & \Phi_u(t) \le -A(1 + u_{\max})^2, \end{cases}
$$

and $v^*$ is given by the same formula with $(B, \Phi_v, v_{\max})$. On the interior regime the strict Legendre condition $\partial^2 H/\partial u^2 > 0$ holds, so the interior stationary point is the unique local minimizer.

So saturating pharmacodynamics with only a linear dose penalty already produces **regular, continuously modulated dosing arcs**. In the control-affine (log-kill) model with the same cost, the Hamiltonian is affine in each control, and extremals are bang–bang except on singular arcs.

## Expansion

$\partial H/\partial u = A + \Phi_u/(1+u)^2$ and $\partial^2 H/\partial u^2 = -2\Phi_u/(1+u)^3$. So $H$ is strictly convex in $u$ exactly when $\Phi_u < 0$, and stationarity gives $(1+u)^2 = -\Phi_u/A$. When $\Phi_u \ge -A$ the Hamiltonian is nondecreasing on $[0, u_{\max}]$; when $\Phi_u \le -A(1+u_{\max})^2$ it is nonincreasing. Projecting the stationary point onto the box gives the three regimes. Because the transcribed optimal control problem is nonconvex, global search (particle swarm) is used to find the switching structure before local SQP refinement.

## Sources

- Bereket Sitotaw Kidane, Md Samiul Haque Motayed, Shuo Wang, "Optimal chemo–immunotherapy scheduling: A hybrid QPSO–SQP approach with Michaelis–Menten pharmacodynamics", Discrete and Continuous Dynamical Systems - B 38 (2026), 280–302, <https://doi.org/10.3934/dcdsb.2026072>. Published version of arXiv:2609.11213, cited next; locators there refer to the arXiv version.
- Bereket Sitotaw Kidane, Md Samiul Haque Motayed, Shuo Wang, "Optimal chemo-immunotherapy scheduling: A hybrid QPSO-SQP approach with Michaelis-Menten pharmacodynamics", arXiv (2026). Section 2 (model), Section 3, Proposition 1, Appendix A (adjoint system), Appendix B (interior arcs). <https://doi.org/10.48550/arXiv.2609.11213>
