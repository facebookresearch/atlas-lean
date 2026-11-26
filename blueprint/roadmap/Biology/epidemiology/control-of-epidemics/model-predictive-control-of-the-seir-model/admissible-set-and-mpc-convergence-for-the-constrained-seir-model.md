# Admissible set and MPC convergence for the constrained SEIR model

**Setting.** Population fractions $S, E, I, R$ follow the controlled SEIR model

$$\dot S = -\beta(t)SI, \qquad \dot E = \beta(t)SI - \eta E, \qquad \dot I = \eta E - \gamma(t)I, \qquad \dot R = \gamma(t)I,$$

with $S + E + I + R = 1$, incubation rate $\eta > 0$, and inputs $\beta(t) \in [\beta_{\min},\beta_{\mathrm{nom}}]$ (social distancing lowers the contact rate) and $\gamma(t) \in [\gamma_{\mathrm{nom}},\gamma_{\max}]$ (quarantine raises the removal rate), $0 < \beta_{\min} < \beta_{\mathrm{nom}}$, $0 < \gamma_{\mathrm{nom}} < \gamma_{\max}$. The state $x = (S,E,I)$ must satisfy the hospital-capacity constraint $I(t) \le I_{\max}$, defining the state set $\mathbb{X}$. Define

- the **admissible set** (viability kernel) $\mathcal{A} = \{x^0 \in \mathbb{X} : \exists$ admissible input with $x(t) \in \mathbb{X}$ for all $t \ge 0\}$;
- the box $\mathbb{X}_{\mathrm{M}} = \{x \in \mathbb{X} : S \le \gamma_{\mathrm{nom}}/\beta_{\mathrm{nom}},\ E \le \gamma_{\mathrm{nom}}I_{\max}/\eta\}$;
- the continuum of disease-free equilibria $\mathcal{E} = \{E = I = 0\}$ and $\mathcal{E}_{\mathrm{nom}} = \mathcal{E} \cap \{S \le \gamma_{\mathrm{nom}}/\beta_{\mathrm{nom}}\}$;
- $\mathcal{A}' = \mathcal{A} \setminus \{x^0 : S^0 \ge \gamma_{\mathrm{nom}}/\beta_{\mathrm{nom}},\ I^0 \le \varepsilon\}$ for a small $\varepsilon \in (0,1]$.

**Lemma (sets).** From every $x^0 \in \mathcal{A}$ some admissible input keeps the state in $\mathbb{X}$ forever with $\lim E = \lim I = 0$ and $\lim S \le \gamma_{\max}/\beta_{\min}$. The box $\mathbb{X}_{\mathrm{M}}$ is robustly invariant: for every admissible input the state stays in $\mathbb{X}_{\mathrm{M}} \subseteq \mathcal{A}$, the cap is never violated, $E$ and $I$ decay exponentially, and $\lim S \le \gamma_{\mathrm{nom}}/\beta_{\mathrm{nom}}$.

**Theorem (MPC without terminal ingredients).** Consider MPC with sampling period $\delta > 0$, prediction horizon $T = N\delta$ and a suitably designed quadratic running cost $\ell$ (penalizing infection and deviation of the inputs from their nominal values), with no terminal cost and no terminal constraint. For every $\delta > 0$ there exist a finite horizon $T$ and $\alpha \in (0,1)$ such that the optimal value function $V_T$ satisfies the relaxed Lyapunov inequality

$$V_T\big(x(\delta;x^0,u^\star)\big) \le V_T(x^0) - (1-\alpha)\int_0^\delta \ell\big(x(s;x^0,u^\star),u^\star(s)\big)\,ds \qquad \text{for all } x^0 \in \mathcal{A}'.$$

Consequently, for $T$ large enough the finite-horizon optimal control problems are recursively feasible from every $x^0 \in \mathcal{A}'$, the closed loop respects the infection cap, and it converges to an equilibrium in $\mathcal{E}_{\mathrm{nom}}$: the admissible set (minus an arbitrarily thin layer) is a domain of attraction of the disease-free equilibria under the MPC feedback.

## Expansion

The key ingredient replacing terminal conditions is cost controllability: on $\mathbb{X}_{\mathrm{M}}$, applying the nominal input makes $E$ and $I$ decay exponentially, so the infinite-horizon value satisfies $V_\infty(x^0) \le \rho\,\ell^\star(x^0)$ for a constant $\rho$, where $\ell^\star$ is the minimal stage cost. Outside the box, any admissible state with not-too-small infection reaches $\mathbb{X}_{\mathrm{M}}$ in uniformly bounded time under maximal intervention, which bounds $V_\infty$ uniformly on $\mathcal{A}'$; the excluded layer contains states with very few infectious individuals and many susceptibles, from which the time to reach the box is unbounded. Standard MPC theory (Grüne–Pannek style) turns these bounds into the relaxed Lyapunov inequality with $\alpha \to 0$ as $T \to \infty$, giving recursive feasibility and asymptotic convergence.

## Sources

- Willem Esterhuizen, Philipp Sauerteig, Stefan Streif and Karl Worthmann, "MPC without Terminal Ingredients Tailored to the SEIR Compartmental Epidemic Model", arXiv:2403.09151 (2024), Section on the constrained SEIR model and sets of interest (lemma on the sets $\mathcal{A}$ and $\mathbb{X}_{\mathrm{M}}$), and the section on MPC without terminal ingredients (cost-controllability proposition and main theorem), <https://doi.org/10.48550/arXiv.2403.09151>. Published version: Systems & Control Letters 193 (2024) 105908, <https://doi.org/10.1016/j.sysconle.2024.105908>.
