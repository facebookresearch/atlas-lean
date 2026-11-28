# Isolation threshold in an epidemic mean-field game

**Agent model.** Each agent's epidemiological state is a continuous-time Markov chain on $\{s, a, i, r, d\}$: susceptible, presymptomatic (infectious but unaware), symptomatic, recovered, dead. The transitions out of $a$ and $i$ have fixed rates $\lambda^{AI}$, $\lambda^{IR}$, $\lambda^{ID}$. The agent picks an activity level $U_t\in[0,1]$, and infection happens at rate

$$
\operatorname{rate}[s\to a] = \lambda^{SA}\,\beta_t\,U_t ,
$$

where $\beta_t\in[0,1)$ is the average activity of infectious agents in the population. The agent minimises the discounted cost

$$
\mathsf J(U;\beta,\alpha) = \mathsf E\!\left(\int_0^T e^{-\gamma t}\bigl(c^{h}(X_t) + c^{a}(X_t)U_t - \alpha_t U_t\bigr)\,dt + e^{-\gamma T}\phi(X_T)\right),
$$

up to the absorption time $T$ in $\{r,d\}$, with discount $\gamma>0$. Here $\alpha_t\in(0,1)$ is the population's average activity, which is also the activity reward. The health costs are $c^h(s)=c^h(a)=0$ and $c^h(i)=1$, the altruistic costs are $c^a(s)=0$ and $c^a(a)=c^a(i)=1$, and $\phi$ is the terminal cost. Define

$$
\bar\phi(i) = \frac{c^h(i) + \lambda^{IR}\phi(r) + \lambda^{ID}\phi(d)}{\gamma + \lambda^{IR} + \lambda^{ID}}, \qquad
\bar\phi(a) = \frac{\lambda^{AI}}{\gamma + \lambda^{AI}}\,\bar\phi(i),
$$

and assume $\bar\phi(i)>0$ (being infected is worse than staying isolated forever).

**Proposition (fully observed agent, stationary mean field).** Suppose $\beta_t\equiv\bar\beta$ and $\alpha_t\equiv\bar\alpha<1$ are constant. Then infected agents ($a$ or $i$) always isolate, $U=0$, and the susceptible agent's optimal control is stationary and of threshold type. Let $\beta^{\mathrm{crit}} = \bar\alpha/(\lambda^{SA}\bar\phi(a))$.

1. If $\bar\beta<\beta^{\mathrm{crit}}$, then $U^{\mathrm{opt}} = 1$ and $v(s) = \dfrac{\lambda^{SA}\bar\beta\,\bar\phi(a) - \bar\alpha}{\lambda^{SA}\bar\beta + \gamma}$.
2. If $\bar\beta\ge\beta^{\mathrm{crit}}$, then $U^{\mathrm{opt}} = 0$ and $v(s) = 0$.

**Proposition (fully observed mean-field equilibrium).** For any initial distribution, the fully observed game has the equilibrium in which presymptomatic and symptomatic agents isolate and susceptibles are fully active. Then $\beta_t = 0$, the susceptible fraction stays at its initial value, and $\alpha_t = \sum_\theta \mathsf p(\theta)\bigl(\rho_0(s;\theta) + \rho_t(r;\theta)\bigr)$, where $\theta$ is an agent attribute such as age.

So with perfect information and rationality transmission stops completely ($R_0 = 0$). Presymptomatic spread arises only when agents cannot observe the presymptomatic state, and then the optimal law depends on the belief $A_t = \mathsf P(X_t = a\mid\text{observations})$.

## Expansion

For $x = i$ and $x = a$ the HJB equations contain $\min_{u}\{c^a(x) - \alpha_t\}u$, and since $c^a = 1>\alpha_t$ the minimiser is $u=0$. The values $\bar\phi(i)$ and $\bar\phi(a)$ then solve linear stationary equations. For $x = s$ the HJB equation is $-\dot v + \gamma v = \min_{u\in[0,1]}\bigl(\lambda^{SA}\beta_t(\bar\phi(a) - v) - \alpha_t\bigr)u$. With constant mean field, the bracket at $v=0$ is negative exactly when $\lambda^{SA}\bar\beta\bar\phi(a)<\bar\alpha$, so full activity is optimal and gives the stated positive-rate value; otherwise isolation gives value zero. At $\beta^{\mathrm{crit}}$ the expected infection cost of activity, $\lambda^{SA}\beta\bar\phi(a)$, balances the activity reward $\bar\alpha$. The discount $\gamma>0$ regularises the problem: at $\gamma = 0$ isolation never ends the episode ($T=\infty$) and the optimal control is not unique. Consistency of the mean field then forces infectious activity, and hence $\beta_t$, to zero.

## Sources

- S. Yagiz Olmez, Shubham Aggarwal, Jin Won Kim, Erik Miehling, Tamer Basar, Matthew West et al., "Modeling Presymptomatic Spread in Epidemics via Mean-Field Games", in 2022 American Control Conference (ACC) (2022), 3648–3655, <https://doi.org/10.23919/acc53348.2022.9867547>. Published version of arXiv:2111.10422, cited next; locators there refer to the arXiv version.
- S. Yagiz Olmez, Shubham Aggarwal, Jin Won Kim, Erik Miehling, Tamer Başar, Matthew West, Prashant G. Mehta, "Modeling Presymptomatic Spread in Epidemics via Mean-Field Games", arXiv 2021: Section 2 (agent and mean-field models, Definition 1), Section 3, Proposition 1, Proposition 2. <https://doi.org/10.48550/arXiv.2111.10422>
