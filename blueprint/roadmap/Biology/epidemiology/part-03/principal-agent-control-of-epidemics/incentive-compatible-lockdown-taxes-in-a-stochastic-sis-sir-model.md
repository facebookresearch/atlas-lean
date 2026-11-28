# Incentive-compatible lockdown taxes in a stochastic SIS/SIR principal-agent model

**Epidemic dynamics.** On $[0,T]$ the susceptible and infected fractions follow the controlled stochastic SIS/SIR model

$$
\begin{aligned}
\mathrm{d}S_t &= \big(\lambda - \mu S_t + \nu I_t - \beta_t\sqrt{\alpha_t}\, S_t I_t\big)\,\mathrm{d}t + \sigma\alpha_t S_t I_t\,\mathrm{d}W_t,\\
\mathrm{d}I_t &= \big(\beta_t\sqrt{\alpha_t}\, S_t I_t - (\mu + \nu + \gamma + \rho) I_t\big)\,\mathrm{d}t - \sigma\alpha_t S_t I_t\,\mathrm{d}W_t,
\end{aligned}
$$

with birth rate $\lambda$, natural death rate $\mu$, disease death rate $\gamma$, recovery-with-immunity rate $\rho$ ($\rho = 0$: SIS) and recovery-without-immunity rate $\nu$ ($\nu = 0$: SIR), and noise intensity $\sigma > 0$. The population chooses its contact (transmission) rate $\beta_t \in B$, which the government cannot observe (moral hazard). The government chooses a testing policy $\alpha_t \in A \subset (0,1]$, where smaller $\alpha$ means more testing and isolation of positives, and a terminal tax $\chi$ that may depend on the observed paths of $(S, I)$.

**Stackelberg game.** Given $(\alpha, \chi)$, the population (agent) solves

$$
V^{\mathrm A}_0(\alpha, \chi) = \sup_\beta \mathbb{E}\Big[\int_0^T u(t, \beta_t, I_t)\,\mathrm{d}t + U(-\chi)\Big],
$$

where $u$ rewards social interaction up to a natural level $\bar\beta$ and penalizes infection, and $U$ is an increasing bijection with $U(0) = 0$. The government (principal) maximizes $\mathbb{E}\big[\chi - \int_0^T (c(I_t) + k(t, \alpha_t, S_t, I_t))\,\mathrm{d}t\big]$ over policies with $V^{\mathrm A}_0 \ge \underline v$ (participation constraint), anticipating the agent's best response.

**Theorem (representation of admissible taxes).** For each admissible policy $(\alpha, \chi)$ there exist a unique $\mathcal{F}_0$-measurable $Y_0$ and a unique process $Z$ in the appropriate $\mathbb{H}^p$ space such that

$$
U(-\chi) = Y_0 - \int_0^T \Big(Z_t(\mu + \nu + \gamma + \rho) I_t + u(t, \beta^\star_t, I_t) - \beta^\star_t\sqrt{\alpha_t}\, S_t I_t Z_t\Big)\,\mathrm{d}t - \int_0^T Z_t\,\mathrm{d}I_t ,
$$

where $\beta^\star_t = b^\star(t, S_t, I_t, Z_t, \alpha_t)$ maximizes $b \mapsto u(t, b, I_t) - b\sqrt{\alpha_t}\, S_t I_t Z_t$. Moreover $\beta^\star$ is the unique optimal response of the population and $V^{\mathrm A}_0(\alpha, \chi) = \mathbb{E}[Y_0]$. Conversely, every pair $(Y_0, Z)$ defines through this formula a tax with the same optimal response, and replacing $Y_0$ by $\mathbb{E}[Y_0]$ leaves the agent's value unchanged.

**Corollary (reduction of the government problem).** The government's problem becomes a standard stochastic control problem over $(\alpha, Z)$ with state $(S, I, Y)$:

$$
V^{\mathrm P}_0 = \sup_{(\alpha, Z)} \mathbb{E}\Big[-U^{-1}\big(Y^{\underline v, Z}_T\big) - \int_0^T \big(c(I_s) + k(s, \alpha_s, S_s, I_s)\big)\,\mathrm{d}s\Big],
$$

where $Y^{\underline v, Z}$ starts at $\underline v$ and evolves by the representation above.

## Expansion

The representation is a backward stochastic differential equation for the agent's continuation utility $Y_t$, driven by the observable infected process. Because $S$ and $I$ are driven by the same Brownian motion with opposite signs, the volatility matrix is degenerate, and the standard condition of continuous-time contract theory (drift proportional to volatility) fails. The proof therefore works with weak formulations on the canonical space and relaxed controls, and uses a martingale representation along $I$. The sensitivity $Z_t$ is the marginal tax per unit of observed infections. The agent's Hamiltonian $u(t, b, I) - b\sqrt{\alpha}\, S I Z$ shows how a larger $Z$ makes contacts costlier and induces voluntary lockdown. Indexing the tax on $S$ instead of $I$ gives an equivalent representation. Once taxes are parametrized by $(Y_0, Z)$, incentive compatibility holds automatically, and the participation constraint binds at $Y_0 = \underline v$; the government's problem is then solved by its HJB equation, numerically in the paper.

## Sources

- Emma Hubert, Thibaut Mastrolia, Dylan Possamaï and Xavier Warin, "Incentives, lockdown, and testing: from Thucydides's analysis to the COVID-19 pandemic", arXiv (2020), Section 2 (stochastic SIS/SIR dynamics, Stackelberg formulation, informal results), Section 4 (Definition 4.1, Theorem 4.7, Lemmas 4.8 and 4.9), <https://doi.org/10.48550/arXiv.2009.00484>.
- J. Cvitanić, D. Possamaï and N. Touzi, "Dynamic programming approach to principal-agent problems", Finance and Stochastics 22 (2018), 1–37, <https://doi.org/10.1007/s00780-017-0344-4>.
