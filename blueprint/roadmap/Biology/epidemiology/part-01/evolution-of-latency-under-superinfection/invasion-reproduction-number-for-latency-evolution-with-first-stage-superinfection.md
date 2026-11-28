# Invasion reproduction number for latency evolution with first-stage superinfection

**Resident model (SIIRS).** Fractions $S, I_1, I_2, R$ of a constant population satisfy

$$\dot S = \delta - \alpha_1 S I_1 - \alpha_2 S I_2 - \delta S + \mu R,\quad \dot I_1 = \alpha_1 S I_1 + \alpha_2 S I_2 - (\nu_1+\delta) I_1,$$

$$\dot I_2 = \nu_1 I_1 - (\nu_2+\delta) I_2,\quad \dot R = \nu_2 I_2 - (\mu+\delta) R,$$

with birth = death rate $\delta$, stage transmission rates $\alpha_i$, progression rates $\nu_i$, and loss of immunity $\mu$. The first-stage rates depend on a latency trait $\lambda \ge 0$:

$$\alpha_1[\lambda] = b_1 F[\lambda]^{-b_2} + \alpha_{1,\infty}, \qquad \nu_1[\lambda] = c_1 F[\lambda]^{-c_2} + \nu_{1,\infty},$$

with $F[0] = 1$, $F[\infty] = \infty$, $F' > 0$ and non-negative constants. If the basic reproduction number exceeds $1$ there is a unique, locally stable endemic equilibrium $(\hat S, \hat I_1, \hat I_2, \hat R)$ with

$$\hat S = \Bigl(\tfrac{\alpha_1}{\nu_1+\delta} + \tfrac{\nu_1}{\nu_1+\delta}\tfrac{\alpha_2}{\nu_2+\delta}\Bigr)^{-1}, \quad \hat I_1 = \frac{1 - \hat S}{1 + \frac{\nu_1}{\nu_2+\delta} + \frac{\nu_2}{\delta+\mu}\frac{\nu_1}{\nu_2+\delta}}, \quad \hat I_2 = \frac{\nu_1}{\nu_2+\delta}\hat I_1 .$$

**Superinfection.** A mutant with latency $\lambda^*$ ($\alpha_1^* = \alpha_1[\lambda^*]$, $\nu_1^* = \nu_1[\lambda^*]$) infects susceptibles and also superinfects resident first-stage hosts with relative propensity $\sigma > 0$, immediately replacing the resident strain; mutant first-stage hosts are likewise superinfected by the resident. Second-stage and recovered hosts cannot be superinfected, and immunity is cross-protective.

**Invasion reproduction number (Equation 2.3).** Linearizing the mutant equations at the resident equilibrium and applying the next-generation method gives

$$\mathcal{R}_0[\lambda,\lambda^*] = \left( \frac{\alpha_1^*}{\nu_1^* + \delta + \sigma \Lambda} + \frac{\nu_1^*}{\nu_1^* + \delta + \sigma \Lambda}\cdot\frac{\alpha_2}{\nu_2+\delta} \right) \bigl(\hat S + \sigma \hat I_1\bigr), \qquad \Lambda = \alpha_1 \hat I_1 + \alpha_2 \hat I_2,$$

with resident quantities evaluated at $\lambda$. The mutant invades iff $\mathcal{R}_0[\lambda,\lambda^*] > 1$.

**Evolutionary outcomes (Section 3.1).** Assume $k = \alpha_2/(\nu_2+\delta) > 1$ and let $\tau = \frac{1}{\nu_2+\delta} + \frac{\nu_2}{\nu_2+\delta}\cdot\frac{1}{\mu+\delta}$ be the mean time a host spends immune to superinfection after leaving the first stage.

- If $c_2 > b_2$ ($\alpha_1$ concave as a function of $\nu_1$), every interior singular strategy is a fitness maximum (an ESS); there is an interior continuously stable strategy or a local attractor at zero latency.
- If $b_2 > c_2$ ($\alpha_1$ convex in $\nu_1$), every interior singular strategy is a fitness minimum. For $\sigma < (1 - \tau\delta)/k$ the outcomes match the model without superinfection (ESS at zero latency, at maximal latency, or bistability). For $(1-\tau\delta)/k < \sigma < (1 + \nu_{1,\infty}\tau)/k$, an intermediate range of $\alpha_{1,\infty}/\delta$ yields a unique evolutionary branching point: convergence stable but invadable, after which strains of different latency are mutually invasible.

## Expansion

Without superinfection the mutant's fitness is its basic reproduction number times $\hat S$, so evolution minimizes the susceptible "resource" and branching is impossible. Superinfection adds the resident first-stage pool $\sigma\hat I_1$ as extra resource for the mutant and the loss rate $\sigma\Lambda$ from being displaced while in the first stage; both depend on the resident trait, making selection frequency-dependent. The thresholds on $\sigma$ compare the superinfection opportunity in the first stage with $k$ and with the fraction $\tau\delta$ of hosts dying while protected. A convergence-stable fitness minimum is an evolutionary branching point; numerically, coexisting coalitions at zero and infinite latency can then be evolutionarily stable.

## Depends on

- [Evolutionary branching point](../../../population-dynamics/classification-of-adaptive-dynamics-singular-str/branching-point.md)

## Sources

- C. M. Saad-Roy, B. T. Grenfell, S. A. Levin, L. Pellis, H. B. Stage, P. van den Driessche, N. S. Wingreen, "Superinfection and the evolution of an initial asymptomatic stage", Royal Society Open Science 8 (2021) 202212, Equations (2.1)–(2.3), (3.1)–(3.2) and Section 3.1, <https://doi.org/10.1098/rsos.202212>, PMCID PMC7890506.
