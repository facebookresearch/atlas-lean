# No gain of entrainment for occupancy models with periodic rates

**Setting.** A system **entrains** to a $T$-periodic input if every trajectory converges to a unique $T$-periodic solution. For an entraining control system with output $h$, compare the average output along the periodic attractor under a $T$-periodic control $u$ with that under the constant control having the same time average. The **gain of entrainment** is the supremum of the improvement over admissible periodic controls with values in $[\ell, L]$, $0 < \ell < L$, and prescribed averages. Augmenting the state with $\xi_j(t) = \int_0^t u_j$ and imposing $x(0) = x(T)$, $\xi_j(T) = T\bar u_j$ turns this into a periodic optimal control problem, solvable with the Pontryagin maximum principle.

**Occupancy model.** In the ribosome flow model with controlled initiation rate $u_0(t)$ and exit rate $u_1(t)$,

$$\dot x_1 = u_0(1 - x_1) - \lambda_1 x_1(1 - x_2),\ \ \dot x_i = \lambda_{i-1}x_{i-1}(1 - x_i) - \lambda_i x_i(1 - x_{i+1}),\ \ \dot x_n = \lambda_{n-1}x_{n-1}(1 - x_n) - u_1 x_n,$$

with $x_i \in [0,1]$ the occupancy of site $i$; $T$-periodic rates are known to entrain the system. The objective is the average production rate $J = \frac{1}{T}\int_0^T u_1(t)\,x_n(t)\,dt$ subject to $\frac{1}{T}\int_0^T u_j = \bar u_j \in (\ell, L)$.

**Theorem.**
1. For the $n$-site problem, constant controls $u_j \equiv \bar u_j$ satisfy the Pontryagin maximum principle with identically zero switching functions (a fully singular extremal); regular arcs of any extremal are bang-bang, $u_j^* \in \{\ell, L\}$.
2. For $n = 1$, $\dot x_1 = u_0(1 - x_1) - u_1 x_1$, every extremal trajectory has $x_1^*(t) \equiv \bar u_0/(\bar u_0 + \bar u_1)$. Hence the constant controls $u_j \equiv \bar u_j$ are optimal and the optimal average production is the constant-input value $\bar u_0\bar u_1/(\bar u_0 + \bar u_1)$: periodic rates give no gain. Optimal controls are not unique, since any $u_j = \bar u_j \rho(t)$ with a common factor $\rho$ and admissible values is also optimal.
3. For $n = 2$ with only the initiation rate $u_0$ controlled and fixed elongation and exit rates $\lambda_1, \lambda_2$, the constant control $u_0 \equiv \bar u_0$ maximizes the average output $\frac1T \int_0^T \lambda_2 x_2\,dt$.
4. (Cascades.) If such a bottleneck module feeds, or is fed by, a positive linear system $\dot z = Az + bw$, $y = c^{\mathsf T}z$ with $A$ Metzler and Hurwitz and $b, c \ge 0$, constant controls still maximize the average output, because the steady-state periodic output of a stable linear system has average $H(0)$ times the input average, $H(s) = c^{\mathsf T}(sI - A)^{-1}b$.

## Expansion

The Hamiltonian is affine in the controls, $H = \varphi_0 u_0 + \varphi_1 u_1$, so off the zero sets of the switching functions the optimal controls are bang-bang. For constant controls the ribosome flow model has a unique globally attracting steady state with nonsingular Jacobian (contraction with respect to a matrix measure), which allows a constant adjoint solution with $\varphi_0 \equiv \varphi_1 \equiv 0$. In one dimension a detailed adjoint analysis excludes regular arcs, forcing $x_1$ to be constant, and existence of an optimum (Filippov's theorem on the compact convex control set) then pins the optimal value. The two-site case reduces to the one-site case by viewing $\lambda_1(1 - x_2)$ as the exit rate of site 1. Biologically, oscillating resource supply cannot raise average protein synthesis in these occupancy models; a gain requires weighted objectives or other mechanisms.

## Sources

- M. Ali Al-Radhawi, M. Margaliot, E. D. Sontag, "Maximizing average throughput in oscillatory biochemical synthesis systems: an optimal control approach", Royal Society Open Science (2021) 210878, Problem 3.1 and Theorem 3.3, Section 4 (model 4.1, Problem 4.1, Lemma 4.2, Theorems 4.3–4.5, Remark 4.6, Problem 4.9, Theorem 4.10) and Section 5 (Proposition 5.1, Theorem 5.2), <https://doi.org/10.1098/rsos.210878>, PMCID PMC8456142.
