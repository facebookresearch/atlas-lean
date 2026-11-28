# Optimal regional quarantine and treatment in a spatial SQEIAR model

Let $\Omega \subset \mathbb{R}^d$, $d \le 3$, be a bounded connected domain with smooth boundary, $\tau > 0$, and let $\omega_1, \dots, \omega_n \subset \Omega$ be disjoint quarantine regions with union $\Omega_n$. The susceptible, quarantined, exposed, asymptomatic, infected and recovered densities $y = (S, Q, E, A, I, R)$ satisfy, with homogeneous Neumann boundary conditions and nonnegative initial data,

$$ \partial_t S = D_1 \Delta S - \Lambda S + \xi R - \chi_{\Omega_n} v S, \qquad \partial_t Q = D_2 \Delta Q + \chi_{\Omega_n} v S, \qquad \partial_t E = D_3 \Delta E - kE + \Lambda S, $$

$$ \partial_t A = D_4 \Delta A - \eta A + (1-z) k E, \qquad \partial_t I = D_5 \Delta I + z k E + (1-p) \eta A - (f + u) I, \qquad \partial_t R = D_6 \Delta R - \xi R + \alpha f I + u I + p \eta A, $$

where $\Lambda = \delta E + (1-q) I + \mu A$ is the force of infection, $D_i > 0$, the parameters $\eta, p, k, z, \alpha, f, \xi$ lie in $[0,1]$, $\xi$ is the reinfection (immunity loss) rate, and the controls are the treatment rate $0 \le u(t,x) \le 1$ and the regional quarantine rate $0 \le v(t,x) \le 1/n$. The cost is

$$ \mathcal{J}(y,u,v) = \int_0^\tau \!\! \int_\Omega \Bigl( \rho_1 \chi_{\Omega_n} S + \rho_3 E + \rho_4 A + \rho_5 I \Bigr) dx\, dt + \frac{\sigma_1}{2} \int_0^\tau \!\! \int_\Omega u^2 \, dx\, dt + \frac{\sigma_2}{2} \int_0^\tau \!\! \int_\Omega \chi_{\Omega_n} v^2 \, dx\, dt. $$

**Theorem.**

1. (Well-posedness, Theorem 3.2) For admissible $(u,v)$ and nonnegative initial data in the domain of the diffusion operator, the system has a unique strong solution with each component in $W^{1,2}(0,\tau; L^2(\Omega)) \cap L^2(0,\tau; H^2(\Omega)) \cap L^\infty(0,\tau; H^1(\Omega))$, nonnegative, and bounded in $L^\infty(\Omega_\tau)$ by a constant independent of the controls.
2. (Existence, Theorem 4.3) The problem of minimizing $\mathcal{J}$ over admissible controls has an optimal solution $(y^*, u^*, v^*)$.
3. (Characterization, Theorems 5.1 and 5.2) The control-to-state map is Gateaux differentiable, and with the adjoint state $P = (p_1, \dots, p_6)$ solving the backward linearized system $-\partial_t P - BP - H^* P = \rho$, $P(\tau) = 0$, where $B$ is the diagonal diffusion operator, $H$ the Jacobian of the reaction terms along $y^*$ and $\rho$ the vector of running weights,

$$ u^*(t,x) = \max\Bigl( 0, \min\Bigl( 1, \frac{I^*(t,x)\,(p_5 - p_6)(t,x)}{\sigma_1} \Bigr) \Bigr), \qquad v^*(t,x) = \max\Bigl( 0, \min\Bigl( \frac{1}{n}, \frac{S^*(t,x)\,(p_1 - p_2)(t,x)}{\sigma_2} \Bigr) \Bigr). $$

## Expansion

The diffusion operator generates a compact contraction semigroup on $L^2(\Omega)^6$ (Proposition 3.1); local Lipschitz reaction terms give a local mild solution, and positivity and an a priori $L^\infty$ bound extend it globally and upgrade it to a strong solution. Existence of an optimum follows from a minimizing sequence: the uniform bounds give compactness of states (Aubin-Lions type), weak-star compactness of controls, and convexity of the quadratic control costs gives lower semicontinuity. Differentiating the state with respect to the controls gives a linear sensitivity system; testing it against the adjoint shows that the directional derivative of $\mathcal{J}$ is $\iint \bigl( (\sigma_1 u^* - I^*(p_5 - p_6)) w_1 + \chi_{\Omega_n} (\sigma_2 v^* - S^*(p_1 - p_2)) w_2 \bigr)$, and nonnegativity over admissible directions yields the projection formulas. Treatment moves mass from $I$ to $R$ and quarantine from $S$ to $Q$, which is why the adjoint differences $p_5 - p_6$ and $p_1 - p_2$ appear.

## Sources

- Mohammed Elghandouri, Khalil Ezzinbi, Youness Mezzan, "Regional control strategies for a spatiotemporal SQEIAR epidemic model: application to COVID-19", International Journal of Control 98 (2025), 2332–2350, <https://doi.org/10.1080/00207179.2025.2456036>. Published version of arXiv:2410.05426, cited next; locators there refer to the arXiv version.
- Elghandouri Mohammed, Ezzinbi Khalil, Youness Mezzan, "Regional Control Strategies for a Spatiotemporal SQEIAR Epidemic Model: Application to COVID-19", arXiv (2024). Section 2 (model), Proposition 3.1, Theorem 3.2, Theorem 4.3, Theorems 5.1 and 5.2. <https://doi.org/10.48550/arXiv.2410.05426>
