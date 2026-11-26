# Steady states of an SIR growth model with health and epidemic-control investment

**Epidemic block.** In a population growing at net rate $b - \mu$ (birth rate $b \ge \mu$, death rate $\mu$), a fraction $p \in [0,1]$ of recruits is vaccinated. In population fractions, with transmission rate $\beta = \beta(A, e, h) \in (0,1]$ and recovery rate $\gamma = \gamma(A,e,h) \in [0,1]$,

$$\dot s = (1-p) b - b s - \beta s i, \qquad \dot i = \beta s i - (\gamma + b) i, \qquad \dot v = p b - b v,$$

where $A$ is direct epidemic-control investment, $e$ the stock of control knowledge and $h$ health capital; $\beta$ is nonincreasing and $\gamma$ nondecreasing in each argument. With $\mathcal{R}_0 = \beta/(b+\gamma)$, for a fixed level of $(A,e,h)$: if $(1-p)\beta < b + \gamma$ there is a single, stable, disease-free state $s^* = 1-p$, $i^* = 0$; otherwise the disease-free state is unstable and the endemic state $s^* = 1/\mathcal{R}_0$, $i^* = \frac{(1-p) b}{\gamma + b} - \frac{b}{\beta}$ is stable (forward bifurcation at $\mathcal{R}_{\mathrm{vac}} = (1-p)\mathcal{R}_0 = 1$).

**Economic block.** A planner maximizes $\int_0^\infty u(c_t) e^{-\theta t}\, dt$ ($u$ increasing, strictly concave, $u'(0^+) = \infty$) over consumption $c$, health spending $m \ge 0$ and control investment $0 \le A \le \bar A$, subject to

$$\dot k = f(k, l) - m - A - c - (\delta_K + b - \mu) k, \qquad \dot h = g(m) - (\delta_H + b - \mu) h, \qquad \dot e = E(A, e) - \delta_E e,$$

with effective labour $l = 1 - i$, a neoclassical production function $f$ satisfying Inada conditions, a concave health technology $g$ with $g(0) = 0$, and a concave knowledge technology $E$ with $E(A,0) = E(0,e) = 0$ and $E_2 \neq \theta + \delta_E$.

**Proposition (steady states).**

1. There is a disease-free steady state with $m^* = h^* = A^* = e^* = 0$, $s^* = 1-p$, $i^* = 0$, capital determined by $f_1(k^*, 1) = \theta + \delta_K + b - \mu$ and $c^* = f(k^*, 1) - (\delta_K + b - \mu) k^*$: without infection the planner spends nothing on health or control.
2. Endemic steady states are exactly the solutions of the endemic condition $(1-p)\beta(A,e,h) > b + \gamma(A,e,h)$, the balance relations $g(m) = (b + \delta_H - \mu) h$, $f_1(k,l) = \theta + \delta_K + b - \mu$, $E(A,e) = \delta_E e$, and complementary-slackness conditions for $m \ge 0$ and $A \ge 0$ that compare the marginal cost $\theta + b + \delta_H - \mu$ (resp. $\theta + \delta_E - E_2$) with the discounted marginal labour gain of reduced infection.
3. (Impatience kills investment) Under monotonicity assumptions on these marginal gains, for each $b \in [\mu, (1-p)\bar\beta - \underline{\gamma})$ (where $\bar\beta, \underline{\gamma}$ are the uncontrolled rates) there are thresholds $\hat\theta_1(b), \hat\theta_2(b)$ such that, if the discount rate exceeds $\hat\theta_{\max}(b) = \max\{\hat\theta_1(b), \hat\theta_2(b), 0\}$, the unique endemic steady state has $m^* = h^* = A^* = e^* = 0$; for intermediate discount rates there are endemic steady states with only one of the two investments positive.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

The epidemic thresholds come from the Jacobian at the disease-free state, whose eigenvalues are $(1-p)\beta - b - \gamma$ and $-b$ (three times); at the endemic state the determinant $b^3((1-p)\beta - (b+\gamma)) > 0$ rules out a nonnegative eigenvalue. For the economic steady states one writes the current-value Hamiltonian and its first-order conditions; at $i^* = 0$ the shadow value of health capital solves $\dot\lambda_2 = \lambda_2 (\theta + b + \delta_H - \mu)$, forcing $\lambda_2^* = 0$ and hence $m^* = 0$, and similarly $A^* = 0$. At an endemic state the multipliers solve a linear system whose determinant involves $(\theta + b + \gamma)(\theta + b + \beta i) - \beta s (\theta + b)$, which yields the closed-form marginal gains; these decrease in $\theta$, so a sufficiently impatient planner finds no investment worthwhile.

## Sources

- Zachariah Sinkala, Vajira Manathunga, Bichaka Fayissa, "An Epidemic Compartment Model for Economic Policy Directions for Managing Future Pandemic", arXiv (2022). Proposition 2.1, Proposition 2.2, Proposition 4.1, Proposition 4.2, Proposition 4.3, Proposition 4.4, Proposition 4.6, Proposition 4.7, Proposition 4.8. <https://doi.org/10.48550/arXiv.2202.05374>
