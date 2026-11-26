# Harvesting stabilization of age-structured rock–paper–scissors competition

**Model.** Three species with age densities $x_i(a,t)$, $a\in(0,A)$, compete cyclically ($x_2$ suppresses $x_1$, $x_3$ suppresses $x_2$, $x_1$ suppresses $x_3$), and species $1$ is harvested (or treated) at a bounded rate $u(t)$:

$$\partial_tx_1 + \partial_ax_1 = -\Big(\mu_1(a) + \int_0^Ag_1(s)x_2(s,t)\,ds + u(t)\Big)x_1, \qquad \partial_tx_2 + \partial_ax_2 = -\Big(\mu_2(a) + \int_0^Ag_2(s)x_3(s,t)\,ds\Big)x_2,$$

$$\partial_tx_3 + \partial_ax_3 = -\Big(\mu_3(a) + \int_0^Ag_3(s)x_1(s,t)\,ds\Big)x_3, \qquad x_i(0,t) = \int_0^Ak_i(a)x_i(a,t)\,da,$$

with mortality $\mu_i \ge 0$, fertility $k_i \ge 0$ and interaction kernels $g_i\in L^2(0,A)$.

**Steady states.** For a constant harvest $u^\ast$, a positive steady state has $x_i^\ast(a) = x_i^\ast(0)\,e^{-\int_0^a(\mu_i + \zeta_i)}$ where each $\zeta_i$ solves the renewal (Euler–Lotka) condition $\int_0^Ak_i(a)e^{-\int_0^a(\mu_i(s)+\zeta_i)\,ds}\,da = 1$, and the interaction levels $\lambda_1 = \int g_3x_1^\ast$, $\lambda_2 = \int g_1x_2^\ast$, $\lambda_3 = \int g_2x_3^\ast$ satisfy $\zeta_1 = \lambda_2 + u^\ast$, $\zeta_2 = \lambda_3$, $\zeta_3 = \lambda_1$; positivity requires $\zeta_1 > u^\ast$, $\zeta_2, \zeta_3 > 0$.

**Reduction and stabilization.** Let $\pi_i$ be the positive adjoint eigenfunction of the renewal operator of species $i$ at the steady state and $\eta_i(t) = \ln\big(\langle\pi_i,x_i(\cdot,t)\rangle/\langle\pi_i,x_i^\ast\rangle\big)$. Then $x_i(a,t) = x_i^\ast(a)\,(1+\psi_i(t-a))\,e^{\eta_i(t)}$ where $\psi_i$ records the deviation of the age profile from its steady shape, and on the invariant set $\psi_i\equiv0$ the dynamics reduce to

$$\dot\eta_1 = u^\ast - u - \lambda_2(e^{\eta_2}-1), \qquad \dot\eta_2 = -\lambda_3(e^{\eta_3}-1), \qquad \dot\eta_3 = -\lambda_1(e^{\eta_1}-1).$$

**Theorem.** There is an explicit bounded feedback $u = u^\ast + \kappa(\eta_1,\eta_2,\eta_3)$, built by backstepping from the functions $\omega_i(\eta_i) = \lambda_i(e^{\eta_i} - 1 - \eta_i)$, under which the reduced system is globally asymptotically stable at $\eta = 0$ (i.e. at the steady state $x^\ast$); the feedback is uniformly bounded, and it is positive (a genuine harvest) for all initial conditions in the largest sublevel set of the control-Lyapunov function contained in an explicit region of $\mathbb R^3$. The same construction extends to the four-species and the general $N$-species non-transitive cycle.

## Depends on

- [Euler–Lotka equation and the reproduction number](../../epidemiology/euler-lotka-equation-and-the-reproduction-number/README.md)
- [Lotka–Volterra predator–prey model](../lotka-volterra-predator-prey-model/README.md)

## Expansion

Pairing the PDE for $x_i$ with the adjoint eigenfunction $\pi_i$ (which solves $\pi_i' - (\mu_i + \zeta_i)\pi_i + \pi_i(0)k_i = 0$, $\pi_i(A) = 0$) kills the transport and renewal terms, leaving $\frac{d}{dt}\ln\langle\pi_i,x_i\rangle$ equal to $\zeta_i$ minus the current interaction and harvest rates; writing interactions relative to their steady values gives the reduced cyclic system with $\phi_i(\eta_i) = \lambda_i(e^{\eta_i}-1)$. Each $\omega_i$ is convex with minimum $0$ at $\eta_i = 0$ and $\dot\omega_i = \phi_i(\eta_i)\dot\eta_i$; since only $\eta_1$ is actuated and the cycle transmits its effect to $\eta_3$ and then $\eta_2$, a backstepping change of variables combining the $\omega_i$ produces a strict control-Lyapunov function and the stabilizing feedback. Positivity of the harvest restricts the guaranteed basin to a sublevel set.

## Sources

- Marius Bargo, Yacouba Simpore, "Stabilization by harvesting in age-structured trophic networks", arXiv (2025). Section "Three-species non-transitive competition" (model, steady states, reduction lemma, stabilization theorem), sections on the four-species case and the $N$-species generalization. <https://doi.org/10.48550/arXiv.2509.02704>
