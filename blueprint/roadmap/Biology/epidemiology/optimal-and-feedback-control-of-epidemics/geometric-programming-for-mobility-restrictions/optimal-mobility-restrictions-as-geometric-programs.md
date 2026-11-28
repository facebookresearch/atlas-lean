# Optimal mobility restrictions as geometric programs

**Model.** A region of $N$ individuals has exposed $E$, symptomatic infected $I$, asymptomatic $A$, hospitalized $H$, recovered $R$ and dead $D$ compartments evolving in discrete time as

$$E(t+1) = (1 - \rho_{EI} - \rho_{EA})E(t) + S_0\,\beta(t)\big(\gamma_A A(t) + I(t)\big), \qquad I(t+1) = (1 - \rho_{IR} - \rho_{IH})I(t) + \rho_{EI}E(t),$$

$$A(t+1) = (1 - \rho_{AR})A(t) + \rho_{EA}E(t), \qquad H(t+1) = (1 - \rho_{HR} - \rho_{HD})H(t) + \rho_{IH}I(t),$$

$$R(t+1) = R(t) + \rho_{IR}I(t) + \rho_{AR}A(t) + (1 - \alpha_D)\rho_{HR}H(t), \qquad D(t+1) = D(t) + \alpha_D\rho_{HR}H(t),$$

with transition probabilities $\rho_{\cdot}$ such that all diagonal coefficients are non-negative, a fixed susceptible level $S_0$ and non-negative initial conditions. The infection rate is set by mobility controls $\mathbf{u}(t) > 0$ (lower values mean stronger restrictions) through a posynomial $\beta(t) = f(\mathbf{u}(t))$, a positive combination of monomials $c\prod_j u_j^{a_j}$ with $c > 0$, $a_j \in \mathbb{R}$.

**Lemma.** For every $t = 0,\dots,T$, the hospitalizations $H(t)$ and deaths $D(t)$ are posynomials in the entries of $\mathbf{u}(0),\dots,\mathbf{u}(T-1)$.

**Theorem (deaths under a budget).** Let $C_t$ be posynomial economic cost functions, $\Gamma$ a budget, $\tau_H$ a hospital capacity, $\gamma_D \in (0,1)$ a discount factor and $\gamma_\infty = \gamma_D^T/(1 - \gamma_D)$, and let the admissible set $\mathcal{U}$ be described by posynomial inequalities and monomial equalities. Then the strategy minimizing $J = \sum_{t=1}^{T-1}\gamma_D^t D(t) + \gamma_\infty D(T)$ subject to $\sum_{t=0}^{T-1}C_t(\mathbf{u}(t)) \le \Gamma$, $H(t) \le \tau_H$ for $t = 1,\dots,T$ and $\mathbf{u}(t) \in \mathcal{U}$ is the solution of a geometric program.

**Theorem (minimal budget).** The minimal budget keeping hospitalizations below capacity is $\Gamma^\star = \sum_t C_t(\mathbf{u}^\star(t))$, where $\mathbf{u}^\star$ minimizes $\sum_t C_t(\mathbf{u}(t))$ subject to $H(t) \le \tau_H$ and $\mathbf{u}(t) \in \mathcal{U}$, again a geometric program; any budget $\Gamma \ge \Gamma^\star$ makes the deaths program feasible.

## Expansion

Posynomials are closed under addition, multiplication and positive scaling. With $S_0$ fixed, the dynamics are linear in the state with coefficients that are either non-negative constants or the posynomial $S_0 f(\mathbf{u}(t))$, so by induction every compartment at time $t$ is a sum of products of non-negative constants and posynomials in earlier controls, hence a posynomial; $D(t)$ accumulates non-negative multiples of $H$. A geometric program, minimizing a posynomial subject to posynomial upper bounds and monomial equalities, becomes a convex program under $y = \log \mathbf{u}$ because log-sum-exp is convex (Hölder's inequality), so the global optimum is computed efficiently. Linearizing at $S_0$ makes the model an upper bound on transmission, which keeps the hospital constraint conservative.

## Sources

- Mikhail Hayhoe, Francisco Barreras, Victor M. Preciado, "Multitask learning and nonlinear optimal control of the COVID-19 outbreak: A geometric programming approach", Annual Reviews in Control 52 (2021), 495–507, <https://doi.org/10.1016/j.arcontrol.2021.04.014>. Published version of arXiv:2011.01392, cited next; locators there refer to the arXiv version.
- Mikhail Hayhoe, Francisco Barreras, Victor M. Preciado, "Data-Driven Control of the COVID-19 Outbreak via Non-Pharmaceutical Interventions: A Geometric Programming Approach", arXiv (2020). Section 2 (posynomials and geometric programs), Section 3 (model), Section 5 (Lemma on posynomials, Theorems on the deaths and minimal-budget programs), Appendix A. <https://doi.org/10.48550/arXiv.2011.01392>
