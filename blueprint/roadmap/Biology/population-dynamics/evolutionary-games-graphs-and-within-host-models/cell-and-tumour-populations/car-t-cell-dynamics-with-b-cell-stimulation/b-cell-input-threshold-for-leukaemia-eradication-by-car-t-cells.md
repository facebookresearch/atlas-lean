# B-cell input threshold for leukaemia eradication by CAR T cells

**Model.** CAR T cells $C$, leukaemic cells $L$ and B cells $B$ (both CD19$^+$, both targeted) evolve as

$$\dot C=C\Big(\rho_C(L+B+I_0)-\frac1{\tau_C}\Big),\qquad \dot L=\rho_LL-\alpha CL,\qquad \dot B=\frac{I_0}{\tau_I}-B\Big(\alpha C+\frac1{\tau_B}\Big),$$

where $\rho_C$ is CAR T-cell stimulation per CD19$^+$ encounter, $\tau_C,\tau_B,\tau_I$ are mean lifetimes (CAR T cells, B cells, B-cell progenitors), $\rho_L$ is leukaemic growth, $\alpha$ is the killing rate, and $I_0$ is the B-cell production from bone marrow (it enters both the B-cell source and CAR T-cell stimulation). Solutions with non-negative data stay non-negative.

**Equilibria.** $P_1=(0,0,I_0\tau_B/\tau_I)$: CAR T cells and leukaemia gone, B-cell homeostasis. $P_2=(C_2,0,\frac1{\tau_C\rho_C}-I_0)$: cure with persistent CAR T cells sustained by B cells. $P_3$: coexistence of all three, with $C_3=\rho_L/\alpha$. $P_1$ is always a saddle (eigenvalue $\rho_L>0$ in the leukaemia direction), and its unstable manifold becomes two-dimensional when $I_0>\frac1{\tau_C\rho_C}\big(1-\frac{\tau_B}{\tau_B+\tau_I}\big)$.

**Theorem (transcritical bifurcations).** At $I_0=\frac1{\tau_C\rho_C}\big(1-\frac{\tau_B}{\tau_B+\tau_I}\big)$ the equilibria $P_1$ and $P_2$ exchange stable and unstable manifold dimensions. At the critical input

$$I_0^{\mathrm{crit}}=\frac1{\tau_C\rho_C}\Big(1-\frac{\tau_B}{\tau_B+\tau_I(1+\tau_B\rho_L)}\Big),$$

$P_2$ and $P_3$ undergo a transcritical bifurcation: for $I_0^{\mathrm{crit}}<I_0<\frac1{\tau_C\rho_C}$ the cure state $P_2$ with persisting CAR T cells is stable and the coexistence state is unstable (for $I_0>\frac1{\tau_C\rho_C}$ the B-cell coordinate of $P_2$ is negative, so $P_2$ lies outside the state space). So sustained B-cell production can secure tumour eradication by keeping CAR T cells stimulated.

**Theorem (oscillations).** At $I_0=0$ the coexistence equilibrium has a subcritical Hopf bifurcation with first Lyapunov coefficient $l_1=\tau_C^{3/2}\rho_C^2/(3\sqrt{\rho_L})>0$, so unstable periodic orbits appear for small $I_0>0$. Trajectories follow an almost heteroclinic cycle between equilibria, with successive leukaemia maxima that explain apparent remission followed by relapse; their size depends on the initial tumour burden.

## Expansion

At $P_1$ the Jacobian is triangular, with eigenvalues $\rho_L$, $-1/\tau_B$ and $\rho_CI_0(1+\tau_B/\tau_I)-1/\tau_C$; the last changes sign at the first threshold, where the CAR T-cell compartment can invade the B-cell-only state, creating $P_2$. Along the cure branch, the leukaemia eigenvalue $\rho_L-\alpha C_2$ crosses zero exactly when $P_3$ leaves the positive orthant, giving $I_0^{\mathrm{crit}}$. Without B-cell input ($I_0=0$) the reduced system is a Lotka-Volterra-like predator-prey loop between CAR T cells and leukaemic cells with a neutral centre, which the input perturbs into weakly unstable oscillations, hence the near-heteroclinic relapse dynamics.

## Sources

- S. Serrano, R. Barrio, Á. Martínez-Rubio, J. Belmonte-Beitia, "Understanding the role of B-cells in CAR T-cell therapy in leukemia through a mathematical model", *Chaos: An Interdisciplinary Journal of Nonlinear Science* 34(8) (2024), 083142, Section 2 (model), Section 3 (Proposition 1, equilibria and their stability, Propositions 2-4, threshold formulas) and Section 4 (successive maxima), <https://doi.org/10.1063/5.0206341> (preprint arXiv:2403.00340).
