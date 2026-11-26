# Stackelberg mean-field equilibrium for SIRS social distancing and vaccination under a budget

**Minor agents.** On $[0,T]$, a representative agent has health state $X_t \in \{S, I, R\}$ and picks a state-dependent socialization level $\alpha_t(e) \in [0,1]$. Infection occurs at rate $\beta\alpha_t(S) Z_t$, where $Z_t$ is the mean socialization of infected agents; recovery at rate $\gamma$; vaccination $S \to R$ at rate $v_t$; waning $R \to S$ at rate $\eta$. Given a government guideline $\lambda_t^e \in [0,1]$, the agent minimizes

$$
J(\alpha; Z) = \mathbb{E}\int_0^T \Big[ (\lambda_t^S - \alpha_t)^2 \mathbf{1}_S(X_t) + \big((\lambda_t^I - \alpha_t)^2 + c_I\big)\mathbf{1}_I(X_t) + (\lambda_t^R - \alpha_t)^2 \mathbf{1}_R(X_t) \Big] dt .
$$

**Proposition (mean-field Nash equilibrium).** The equilibrium controls are $\hat\alpha_t(S) = \lambda_t^S + \tfrac{\beta Z_t}{2}(u_t(S) - u_t(I))$, $\hat\alpha_t(I) = \lambda_t^I$, $\hat\alpha_t(R) = \lambda_t^R$. Here the state law $p_t$ solves the forward Kolmogorov equations

$$
\dot p(S) = -\beta\hat\alpha(S) Z p(S) - v p(S) + \eta p(R), \quad \dot p(I) = \beta\hat\alpha(S) Z p(S) - \gamma p(I), \quad \dot p(R) = \gamma p(I) + v p(S) - \eta p(R),
$$

and the value function $u_t$ solves the backward HJB system

$$
\dot u(S) = \beta\hat\alpha(S) Z (u(S) - u(I)) + v(u(S) - u(R)) - (\lambda^S - \hat\alpha(S))^2, \quad \dot u(I) = \gamma(u(I) - u(R)) - c_I, \quad \dot u(R) = \eta(u(R) - u(S)),
$$

with $u_T = 0$, $p_0 = \pi_0$, and consistency $Z_t = \hat\alpha_t(I) p_t(I)$. For a short enough horizon $T$, this forward–backward system has a unique bounded solution.

**Principal.** A government chooses open-loop policies $\theta_t = (\lambda_t^S, \lambda_t^I, \lambda_t^R, v_t) \in [0,1]^3 \times [0,V]$, has a budget $dB_t = b(t, \theta_t, p_t^\theta)\, dt$ with $B_0 = b_0$, and minimizes $J_G(\theta) = \int_0^T [\Phi_p(p_t^\theta(I)) + \Phi_\lambda(\lambda_t) + \Phi_v(v_t)]\, dt + \Psi(B_T)$, where $\Psi$ penalizes a terminal deficit. A minimizer is a **Stackelberg mean-field equilibrium**.

**Theorem.** Under a short enough horizon, the principal's Hamiltonian is strongly convex in $(\lambda^S, \lambda^I)$ and has a unique minimizer. Any Stackelberg equilibrium satisfies a linear system for $(\lambda^{S*}, \lambda^{I*})$ in terms of the states and co-states of an extended forward–backward ODE system, and that extended system has a unique bounded continuous solution.

## Expansion

For fixed $Z$ and policies, the agent's problem is a finite-state controlled Markov chain. Pointwise minimization of the quadratic Hamiltonian gives the feedback formula, and dynamic programming gives the HJB system. Coupling it with the Kolmogorov equations and the fixed-point condition on $Z$ yields a forward–backward ODE system. Its coefficients are Lipschitz on bounded sets, so a contraction argument on a short horizon gives uniqueness, which makes the principal's problem well-posed. The principal then solves a deterministic optimal control problem whose state is the equilibrium flow $(p, u)$ together with the budget. Pontryagin's principle adds co-states $(\varphi, \psi, \chi)$, and the short horizon keeps the co-state contributions small enough that the Hamiltonian stays strongly convex.

## Sources

- Huaning Liu, Gokce Dayanikli, "Epidemic Control using Stackelberg Mean Field Game with Budget Constraint", arXiv (2026). Definition 2.1, Proposition 2.2, Proposition 2.3, Definitions 2.4-2.5, Theorem 3.1, Lemma 3.2, Theorem 3.3. <https://doi.org/10.48550/arXiv.2609.19641>
