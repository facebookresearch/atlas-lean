# Positivity and L1 stability of the kinetic SEIR model with contact heterogeneity

**Model.** For each compartment $J \in \{S, E, I, R\}$, $f_J(\mathbf{z}, x, t)$ is the density of individuals with $x \ge 0$ social contacts, where $\mathbf{z}$ collects uncertain social parameters. Contact behavior relaxes on a time scale $\tau$ through the Fokker–Planck operator

$$Q_J(f_J) = \partial_x\Big[A_J(\mathbf{z},x) f_J + \partial_x\big(B_J(\mathbf{z},x) f_J\big)\Big], \qquad A_J = \frac{\mu}{2\delta}x^{1-\alpha(\delta)}\Big[\Big(\frac{x}{m_J}\Big)^{\delta} - 1\Big], \quad B_J = \frac{\sigma^2}{2}x^{2-\alpha(\delta)},$$

which conserves mass and drives the mean number of contacts $m_J$ toward its target, with $\delta = \delta(\mathbf{z})$ shaping the tail of the equilibrium contact distribution. Transmission depends on contacts through a kernel $\kappa(x, x_*) \ge 0$:

$$\partial_t f_S = -K(f_S, f_I) + \tfrac1\tau Q_S(f_S), \qquad \partial_t f_E = K(f_S, f_I) - \zeta f_E + \tfrac1\tau Q_E(f_E),$$

$$\partial_t f_I = \zeta f_E - \gamma f_I + \tfrac1\tau Q_I(f_I), \qquad \partial_t f_R = \gamma f_I + \tfrac1\tau Q_R(f_R), \qquad K(f_S, f_I) = f_S(x)\int_0^\infty \kappa(x, x_*)\, f_I(x_*)\, dx_*.$$

**Theorem.**

1. *(L1 contraction of contact relaxation.)* If $f_J^0 \in L^1(\mathbb{R}_+)$ for all $\mathbf{z}$, the solution of $\partial_t f_J = Q_J(f_J)$ has $\int_0^\infty |f_J|\, dx$ nonincreasing in $t$; consequently nonnegative initial data remain nonnegative.
2. *(Positivity of the transmission step.)* Solutions of the contact-structured SEIR system without relaxation ($\partial_t f_S = -K$, $\partial_t f_E = K - \zeta(x) f_E$, $\partial_t f_I = \zeta(x) f_E - \gamma(x) f_I$, $\partial_t f_R = \gamma(x) f_I$) with nonnegative data stay nonnegative for all $t \ge 0$.
3. *(Uniqueness and stability.)* For constant $\beta, \zeta, \gamma > 0$ and $\|\kappa\|_{L^\infty} \le \bar\kappa$, any two solutions with $L^1$ initial data satisfy, for some $C^{\max} > 0$,

$$\sum_{J} \|f_J(\cdot, t) - g_J(\cdot, t)\|_{L^1(\mathbb{R}_+)} \le e^{C^{\max} t}\sum_{J}\|f_J(\cdot, 0) - g_J(\cdot, 0)\|_{L^1(\mathbb{R}_+)},$$

so the kinetic model has at most one solution for given initial data, uniformly in the uncertain parameters $\mathbf{z}$.

## Depends on

- [Solution of the closed SEIR system for times t ≥ 0](../../seir-epidemic-model/is-solution.md)

## Expansion

The Fokker–Planck operator is in divergence form, so testing with a regularized sign function of $f_J$ and integrating by parts gives a nonpositive time derivative of the $L^1$ norm (Kato's inequality); applied to the negative part, it gives positivity. In the transmission step $f_S$ solves a linear equation with nonnegative rate $\int \kappa f_I$, hence stays nonnegative, and $f_E$, $f_I$, $f_R$ are driven by nonnegative sources minus linear losses. For uniqueness, subtract the equations for two solutions, write $K(f_S, f_I) - K(g_S, g_I) = (f_S - g_S)\int\kappa f_I + g_S\int\kappa (f_I - g_I)$, bound it in $L^1$ by $\bar\kappa$ times the masses, use the contraction of $Q_J$, and close with Gronwall's inequality. With $\varphi(x) = x$ the relaxation drives the mean contacts $m_J$ to equilibrium in the quasi-invariant limit, and controls that penalize high contact numbers can force slim-tailed equilibrium contact distributions.

## Sources

- Jonathan Franceschi, Andrea Medaglia, Mattia Zanella, "On the optimal control of kinetic epidemic models with uncertain social features", Optimal Control Applications and Methods 45 (2024), 494–522, <https://doi.org/10.1002/oca.3029>. Published version of arXiv:2210.09201, cited next; locators there refer to the arXiv version.
- Jonathan Franceschi, Andrea Medaglia, Mattia Zanella, "On the optimal control of kinetic epidemic models with uncertain social features", arXiv (2022). Remark 2.1, Proposition 2.3, Corollary 2.4, Proposition 2.5, Theorem 2.6, Remark 3.1. <https://doi.org/10.48550/arXiv.2210.09201>
