# Critical transmission level for a rational susceptible agent

**Model.** A single agent's epidemiological state $X_t \in \{s, a, i, r, d\}$ (susceptible, asymptomatic infectious, symptomatic infectious, recovered, dead) is a continuous-time Markov chain with transitions $a \to i$, $a \to r$, $i \to r$, $i \to d$ at fixed rates $\lambda^{AI}, \lambda^{AR}, \lambda^{IR}, \lambda^{ID}$, and infection rate

$$ \text{rate}[s \to a] = \eta + \lambda^{SA} \beta_t U_t, $$

where $U_t \in [0,1]$ is the agent's activity level, $\eta > 0$ a baseline rate, $\lambda^{SA}$ the transmissibility, and $\beta_t \in [0,1]$ the average activity of infected agents in the population (the mean-field process, $\beta_t = \sum_\theta p(\theta) \sum_{x \in \{a,i\}} \int_0^1 u\, \rho_t(x,u;\theta)\, du$). The agent minimizes the discounted cost $\mathsf{E}\bigl[\int_0^T e^{-\gamma t} c(X_t, U_t)\, dt + e^{-\gamma T} \bar\phi(X_T)\bigr]$ up to the absorption time $T$ in $\{r, d\}$, where activity earns an economic reward $\alpha$ per unit time and, in the infectious states, carries an altruistic cost $1$ per unit time, and $\bar\phi(r), \bar\phi(d)$ are given terminal costs.

**Theorem.** Assume $\alpha < 1$ and the state is fully observed.

1. (Proposition 1) In states $a$ and $i$ the optimal activity is $0$ and the value function is stationary, $\bar\phi(a) = \dfrac{c^h(a) + \lambda^{AI} \bar\phi(i) + \lambda^{AR} \bar\phi(r)}{\gamma + \lambda^{AI} + \lambda^{AR}}$, $\bar\phi(i) = \dfrac{c^h(i) + \lambda^{IR} \bar\phi(r) + \lambda^{ID} \bar\phi(d)}{\gamma + \lambda^{IR} + \lambda^{ID}}$, with $c^h$ the health cost. In state $s$ the value function solves the HJB equation

$$ -\frac{d v_t(s)}{dt} + (\gamma + \eta)\, v_t(s) = \eta\, \bar\phi(a) + \min_{u \in [0,1]} \Bigl( \lambda^{SA} \beta_t \bigl( \bar\phi(a) - v_t(s) \bigr) - \alpha \Bigr) u. $$

2. (Proposition 3) Suppose also $\gamma > 0$, $\bar\phi(i) > 0$ and $\beta_t \equiv \bar\beta$. Set

$$ \bar\beta^{\mathrm{crit}} = \frac{\alpha}{\lambda^{SA} \bar\phi(a)} \Bigl( 1 + \frac{\eta}{\gamma} \Bigr). $$

If $\bar\beta < \bar\beta^{\mathrm{crit}}$, the optimal susceptible policy is $U \equiv 1$ with $v(s) = \dfrac{(\lambda^{SA} \bar\beta + \eta) \bar\phi(a) - \alpha}{\lambda^{SA} \bar\beta + \gamma + \eta}$; if $\bar\beta \ge \bar\beta^{\mathrm{crit}}$, it is $U \equiv 0$ with $v(s) = \dfrac{\eta}{\gamma + \eta} \bar\phi(a)$.

3. (Proposition 6) In the mean-field game where every agent is fully observed, the unique mean-field equilibrium is $\beta_t = 0$ for all $t \ge 0$.

## Expansion

Since the reward $\alpha$ is below the altruistic cost $1$, any infected agent who knows its state prefers isolation, which gives the stationary values in states $a$ and $i$ by first-step analysis. For a susceptible agent the HJB is linear in $u$, so the optimal control is bang-bang: be active exactly when the marginal infection risk $\lambda^{SA} \bar\beta (\bar\phi(a) - v(s))$ is below the reward $\alpha$. In the stationary case one solves for $v(s)$ under each policy and checks self-consistency; the switch occurs at $\lambda^{SA} \bar\beta\, \gamma \bar\phi(a) / (\gamma + \eta) = \alpha$, which is $\bar\beta = \bar\beta^{\mathrm{crit}}$. With full observation every infected agent isolates, so the average activity of infected agents is identically zero, and this is the only fixed point of the best-response map. Partial observation of the asymptomatic state breaks this conclusion.

## Sources

- S. Yagiz Olmez, Shubham Aggarwal, Jin Won Kim, Erik Miehling, Tamer Basar, Matthew West et al., "How does a Rational Agent Act in an Epidemic?", in 2022 IEEE 61st Conference on Decision and Control (CDC) (2022), 5536–5543, <https://doi.org/10.1109/cdc51059.2022.9992844>. Published version of arXiv:2206.02222, cited next; locators there refer to the arXiv version.
- S. Yagiz Olmez, Shubham Aggarwal, Jin Won Kim, Erik Miehling, Tamer Başar, Matthew West, Prashant G. Mehta, "How does a Rational Agent Act in an Epidemic?", arXiv (2022). Propositions 1, 3 and 6, Table 1, Sections 2-5. <https://doi.org/10.48550/arXiv.2206.02222>
