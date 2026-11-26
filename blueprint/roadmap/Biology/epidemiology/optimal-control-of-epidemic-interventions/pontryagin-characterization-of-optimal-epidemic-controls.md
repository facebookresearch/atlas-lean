# Pontryagin characterization of optimal epidemic controls

**Problem.** A compartmental model $\dot x = f(x, u)$, $x(0) = x_0$, with state $x \in \mathbb R^n_{\ge 0}$ is controlled by Lebesgue-measurable $u = (u_1, \dots, u_m) : [0, T_f] \to [0, 1]^m$, where each $u_j$ enters $f$ affinely (for example, enhanced quarantine of exposed individuals at rate $(1 + u_1)\kappa E$, enhanced isolation of infectious individuals at rate $(1 + u_2)\eta I$, or vaccination moving susceptibles at rate $u_j S$). Minimize
$$J(u) = \int_0^{T_f} \Bigl( \sum_{i} A_i x_i(t) + \tfrac12 \sum_{j=1}^{m} B_j u_j(t)^2 \Bigr) dt,$$
where the $A_i \ge 0$ weight the infected compartments and $B_j > 0$ are relative intervention costs.

**Existence.** Because the control set is closed, convex and bounded, the state equations are affine in $u$ with bounded solutions, and the integrand is convex in $u$ with superlinear growth, an optimal control exists (Fleming–Rishel conditions).

**Necessary conditions.** With Hamiltonian $H = \sum_i A_i x_i + \tfrac12 \sum_j B_j u_j^2 + \lambda^{\mathsf T} f(x, u)$, an optimal pair $(x^*, u^*)$ admits adjoint variables solving
$$\dot\lambda = -\frac{\partial H}{\partial x}(x^*, u^*, \lambda), \qquad \lambda(T_f) = 0 \ \ (\text{transversality}),$$
and minimizing $H$ pointwise over $[0,1]^m$ gives
$$u_j^*(t) = \min\Bigl\{1,\ \max\Bigl\{0,\ -\frac{1}{B_j} \sum_{i} \lambda_i(t)\, \frac{\partial f_i}{\partial u_j}(x^*(t))\Bigr\}\Bigr\}.$$
For the quarantine control acting on $\kappa E$ (moving exposed individuals from $E$ to quarantine $Q$) this reads
$$u_1^* = \min\Bigl\{1, \max\Bigl\{0, \frac{\kappa E^* (\lambda_E - \lambda_Q)}{B_1}\Bigr\}\Bigr\},$$
and for a vaccination control moving $S$ to $V$, $u^* = \min\{1, \max\{0, S^*(\lambda_S - \lambda_V)/B\}\}$.

## Expansion

Since $f$ is affine in $u$, $\partial H / \partial u_j = B_j u_j + \sum_i \lambda_i \partial f_i / \partial u_j$ is strictly increasing in $u_j$, so the unconstrained stationary point is unique and projection onto $[0,1]$ gives the pointwise minimizer. The adjoint $\lambda_i$ is the shadow cost of one more individual in compartment $i$; the control is high when moving people between compartments reduces future cost (for quarantine, $\lambda_E > \lambda_Q$) and when the compartment acted on is large, and it switches off near $T_f$ as the adjoints vanish. The forward-backward system is solved numerically by forward-backward sweeps. In a COVID-19 model with asymptomatic, quarantined, hospitalized and critical classes, controls on contact tracing and isolation were chosen as the parameters with largest partial rank correlation with $\mathcal R_0$; in a COVID-19–influenza co-infection model, combining a non-pharmaceutical control with vaccination controls for each pathogen reduced both infections more than any single or paired control.

## Sources

- S. Ullah, M. A. Khan, "Modeling the impact of non-pharmaceutical interventions on the dynamics of novel coronavirus with optimal control analysis with a case study", Chaos, Solitons & Fractals (2020), Section 7 (control system Eq. 13, objective functional, Hamiltonian Eqs. 15–16, Pontryagin conditions Eq. 17) and Theorem 3 (adjoint system Eq. 18, control characterization Eq. 19). <https://doi.org/10.1016/j.chaos.2020.110075> (PMC7341999).
- M. M. Ojo, T. O. Benson, O. J. Peter, E. F. D. Goufo, "Nonlinear optimal control strategies for a mathematical model of COVID-19 and influenza co-infection", Physica A (2022), optimal control problem (three time-dependent controls: non-pharmaceutical prevention and vaccination against each pathogen; adjoint system and transversality conditions, control characterization Eqs. 37–39). <https://doi.org/10.1016/j.physa.2022.128173> (PMC9461290).
