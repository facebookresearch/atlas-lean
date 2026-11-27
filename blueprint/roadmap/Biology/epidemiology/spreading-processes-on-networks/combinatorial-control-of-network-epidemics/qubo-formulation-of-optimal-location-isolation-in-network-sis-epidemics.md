# QUBO formulation of optimal location isolation in network SIS epidemics

**Setting.** A population is split into $M$ locations of sizes $n_i$, coupled by a mobility matrix $A = (A_{ij}) \ge 0$. In the discrete-time network SIS model, with recovery probability $\mu$ and infection rate $\lambda$, the number infected in location $i$ evolves as

$$x_i(t+1) = (1-\mu)\,x_i(t) + \frac{\lambda}{n_i}\big(n_i - x_i(t)\big)\,\alpha_i(\mathbf{u},t), \qquad \alpha_i(\mathbf{u},t) = x_i(t) + (1 - u_i)\sum_{j} A_{ij}x_j(t),$$

where the binary control $u_i \in \{0,1\}$ isolates location $i$ (its residents can be infected only within the location). Over a window of $T$ steps the cost is

$$f(\mathbf{x},\mathbf{u}) = \sum_{i}\sum_{t=1}^{T} x_i(t) + \gamma\sum_i n_i u_i,$$

balancing infections against the population affected by isolation, $\gamma \ge 0$.

**Proposition (well-posedness).** If $\lambda \le \max_i\big(1 + \sum_j A_{ij}\,n_j/n_i\big)^{-1}$, the box $\prod_i [0,n_i]$ is positively invariant, with or without control.

**Theorem (two-step horizon).** For $T = 2$ and initial state $\bar{\mathbf{x}} = \mathbf{x}(0)$, the optimal isolation policy is $\mathbf{u}^\ast = \mathbf{1} - \mathbf{z}^\ast$, where $\mathbf{z}^\ast$ solves the quadratic unconstrained binary optimisation (QUBO) problem

$$\mathbf{z}^\ast = \arg\min_{\mathbf{z}\in\{0,1\}^M} \sum_i P_i z_i + \sum_{i}\sum_{j \ne i} Q_{ij}\,z_i z_j,$$

with explicit coefficients determined by $\lambda, \mu, \gamma, A, \mathbf{n}$ and $\bar{\mathbf{x}}$: each linear coefficient $P_i$ collects the first- and second-step infections caused by keeping location $i$ open, minus the saved isolation cost $\gamma n_i$, and

$$Q_{ij} = \lambda^2 A_{ij}\Big[1 - \frac{\bar x_i}{n_i}\Big(1 - \mu + \lambda\Big(1 - \frac{\bar x_i}{n_i}\Big)\Big) - \frac{\lambda}{n_i}\Big(1 - \frac{\bar x_i}{n_i}\Big)\sum_k A_{ik}\bar x_k\Big]\Big(1 - \frac{\bar x_j}{n_j}\Big)\sum_k A_{jk}\bar x_k .$$

The same holds for the network SIR model, with susceptibles $n_i - x_i - y_i$ and modified $P_i, Q_{ij}$.

## Expansion

With $z_i = 1 - u_i$ ("open"), $x_i(1)$ is affine in $z_i$ alone, because the controlled force of infection at time $0$ depends only on the initial state; $x_i(2)$ then involves $z_i$ times $x_j(1)$ and $z_i$ times $x_i(1)$, which makes it quadratic in $\mathbf{z}$, and $z_i^2 = z_i$ for binary variables folds the diagonal terms into $P_i$. Summing over locations gives a QUBO, the native input of quantum annealers and of quantum approximate optimisation, so the epidemic-control problem can be solved on quantum hardware or by classical QUBO solvers. The coupling $Q_{ij}$ is nonzero only when $i$ draws infection from $j$'s neighbourhood ($A_{ij} > 0$), and it captures that opening two connected locations together is worse than the sum of opening each. For $T > 2$ the objective becomes a higher-degree polynomial in $\mathbf{z}$; the paper suggests auxiliary variables or Taylor approximations, and a rolling-horizon (model-predictive) use of the $T = 2$ problem for time-varying interventions.

## Sources

- Lorenzo Zino, Mattia Boggio, Deborah Volpe, Giacomo Orlandi, Giovanna Turvani, Carlo Novara, "A Quantum-Compliant Formulation for Network Epidemic Control", in 2025 IEEE 64th Conference on Decision and Control (CDC) (2025), 3818–3828, <https://doi.org/10.1109/cdc57313.2025.11312245>. Published version of arXiv:2509.00337, cited next; locators there refer to the arXiv version.
- Lorenzo Zino, Mattia Boggio, Deborah Volpe, Giacomo Orlandi, Giovanna Turvani, Carlo Novara, "A Quantum-Compliant Formulation for Network Epidemic Control", arXiv:2509.00337 (2025), Section 2 (network SIS and SIR models, Remark 1, Proposition 1, control), Section 3 (Problem 1) and Section 4 (Theorems 1 and 2, Remark 3), <https://doi.org/10.48550/arXiv.2509.00337>.
