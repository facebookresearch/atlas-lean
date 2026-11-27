# Global boundedness of the virus–T-cell reaction–diffusion model with nonlocal inflow

**Model.** On a bounded domain $\Omega$ (an organ, e.g. the liver) with homogeneous Neumann boundary conditions, a virus density $u(t,\mathbf x)$ and a T-cell density $v(t,\mathbf x)$ satisfy the predator–prey system

$$u_t = u\,w(u) - \gamma u v + \alpha \Delta u, \qquad v_t = j[u] - \eta(1-u)v + \beta \Delta v,$$

with logistic growth with a strong Allee effect

$$w(u) = (1-u)\frac{u - u_{\min}}{u + \kappa}, \qquad 0 < u_{\min} \ll 1,\ \kappa > 0,$$

and a **nonlocal inflow** of T cells, produced elsewhere (lymph nodes) in proportion to the total viral load and entering through a subregion $\Theta \subset \Omega$:

$$ju = \delta\,\chi_\Theta(\mathbf x)\,U(t), \qquad U(t) = \int_\Omega u(t,\mathbf x)\,d\mathbf x,$$

where $\chi_\Theta \ge 0$ is bounded, piecewise continuous, supported in $\Theta$ and integrates to $1$. Constants $\alpha, \beta, \gamma, \delta, \eta > 0$; $\gamma u v$ is the killing of virus by T cells and $\eta(1-u)v$ the fading of the immune response in the absence of virus.

**Theorem.** For bounded initial data $0 \le u_0 \le 1$, $0 \le v_0 \le v_{\max}$:

1. weak solutions exist with $u, v \in L^2(0,T; H^1(\Omega))$ as long as they stay bounded, and they satisfy $0 \le u \le 1$ and $v \ge 0$ (initial values $u_0 > 1$ fall below $1$ in finite time);
2. the totals $(U(t), V(t))$, $V = \int_\Omega v$, remain for all times in the trapezoid

$$\Sigma = \Big\{(U,V) : 0 \le U \le |\Omega|,\ 0 \le V \le V_{\mathrm{up}} - \frac{\eta}{\gamma}U\Big\}, \qquad V_{\mathrm{up}} = \frac1\gamma\Big(\eta + 1 + \frac{\gamma\delta}{\eta}\Big)|\Omega|,$$

for suitable initial totals;
3. $\|v(t)\|_{L^2(\Omega)}$ stays bounded for all $t > 0$, and $v$ is bounded in $L^\infty$ by a finite $v_{\max}$.

Hence solutions exist for all time and neither the virus nor the immune response blows up, despite the nonlocal, unbounded-looking feedback from total viral load to T-cell influx.

## Expansion

Nonnegativity and $u \le 1$ follow from comparison principles, since $w(1) = 0$ and $w < 0$ for $u > 1$. Integrating the equations over $\Omega$ (the diffusion terms vanish under the Neumann condition) gives an ODE system for $(U, V)$ with the inflow contributing exactly $\delta U$; the key estimate is that eventually $\int_\Omega u v^\varrho \le \theta \int_\Omega v^\varrho$ for some $\theta < 1$, so the decay term $\eta(1-u)v$ dominates on average, which yields the invariant trapezoid. $L^2$ bounds on $v$ come from an energy estimate, and the $L^\infty$ bound from bounding $|\Delta v|$ for the linear parabolic equation $v_t = \beta\Delta v - a v + f$ with $a \ge 0$ and bounded $f$, together with the $L^1$ bound.

## Sources

- Cordula Reisch, Dirk Langemann, "Longterm existence of solutions of a reaction diffusion system with non-local terms modeling an immune response — an interpretation-orientated proof", arXiv (2020). Section 2 (model, growth and inflow functions), Theorem 6, Lemmas 7, 8 and 12, Corollaries 9–11, Theorems 13, 16 and 23. <https://doi.org/10.48550/arXiv.2008.01435>. Published version: Partial Differential Equations in Applied Mathematics 6 (2022), article 100446, <https://doi.org/10.1016/j.padiff.2022.100446>; locators above refer to the arXiv version.
