# Threshold isolation policy under unobserved asymptomatic infection

Consider the agent model of the critical-transmission article: states $\{s, a, i, r, d\}$, infection rate $\eta + \lambda^{SA} \beta_t U_t$, reward $\alpha < 1$ for activity and altruistic cost $1$ for activity while infectious. Now the agent observes only $Y_t = 1_{[X_t = i]} + 2 \cdot 1_{[X_t = d]}$, so it cannot distinguish $s$, $a$ and $r$ until symptoms appear at the stopping time $\tau = \inf\{t : X_t = i\}$. For $t < \tau$ its belief $S_t = \Pr(X_t = s \mid \mathcal{Y}_t)$, $A_t = \Pr(X_t = a \mid \mathcal{Y}_t)$, $R_t = 1 - S_t - A_t$ evolves by the nonlinear filter

$$ \dot S_t = \bigl( -\lambda^{SA} \beta_t U_t - \eta + \lambda^{AI} A_t \bigr) S_t, \qquad \dot A_t = \bigl( \lambda^{SA} \beta_t U_t + \eta \bigr) S_t + A_t \bigl( -\lambda^{AI} - \lambda^{AR} + \lambda^{AI} A_t \bigr), $$

and the value function $\phi_t(s,a)$ of the belief-state problem solves an HJB equation $(-\partial_t \phi_t + \gamma \phi_t)(s,a) = (\mathcal{L}\phi_t)(s,a) + \min_{u \in [0,1]} \mathcal{M}_t(s,a)\, u$ (Proposition 2).

**Theorem.** Let $\beta_t \equiv \bar\beta$ and let $\bar\beta^{\mathrm{crit}} = \frac{\alpha}{\lambda^{SA} \bar\phi(a)}(1 + \eta/\gamma)$ be the fully observed critical level.

1. (Belief ceiling, Proposition 5) Set $\bar a = (\lambda^{SA} \bar\beta + \eta)/\lambda^{AI}$. If the agent starts susceptible ($S_0 = 1$) and stays active ($U_s = 1$ for $s < t$), then $A_t < \bar a$ for all $0 \le t < \tau$; if moreover $\lambda^{AR} = 0$, then $A_t \uparrow \min\{\bar a, 1\}$ as $t \to \infty$.
2. (Threshold policy, Proposition 4) Assume $S_0 + A_0 = 1$ and $\lambda^{AR} = 0$, so that $S_t + A_t = 1$ for $t < \tau$ and the belief is the single number $A_t$. If $\bar\beta \ge \bar\beta^{\mathrm{crit}}$, the optimal policy is to isolate, $\bar\psi(\cdot, a) = 0$. If $\bar\beta < \alpha / (\lambda^{SA} \bar\phi(i)) < \bar\beta^{\mathrm{crit}}$, there is $\underline\lambda^{AI}(\bar\beta)$ such that for all $\lambda^{AI} > \underline\lambda^{AI}(\bar\beta)$ the optimal policy is of threshold type,

$$ \bar\psi(\cdot, a) = 1 \ \text{ for } 0 \le a < a^{\mathrm{thresh}}, \qquad \bar\psi(\cdot, a) = 0 \ \text{ for } a^{\mathrm{thresh}} < a \le 1, $$

with $a^{\mathrm{thresh}} \in (0,1)$ and $\lambda^{SA} \bar\beta / \lambda^{AI} < a^{\mathrm{thresh}}$. The function $\underline\lambda^{AI}$ is monotone and $\underline\lambda^{AI}(\bar\beta) \to 0$ as $\bar\beta \downarrow 0$.

When symptoms appear fast relative to infection ($\lambda^{AI}$ large), an active susceptible agent's belief of being asymptomatically infected stays below the isolation threshold, so a fully rational agent keeps unknowingly infectious agents active; this is how limited information on viral state sustains epidemic growth in the mean-field game.

## Depends on

- [Critical transmission level for a rational susceptible agent](critical-transmission-level-for-a-rational-susceptible-agent.md)

## Expansion

The filter is the Wonham-type filter of the chain conditioned on no symptoms: probability mass flows from $s$ to $a$ at the infection rate and is renormalized by the conditional survival of "no symptoms", which produces the quadratic term $\lambda^{AI} A_t^2$. With $U \equiv 1$, $\lambda^{AR} = 0$ and $S_t = 1 - A_t$, the belief equation becomes $\dot A_t = (1 - A_t)\bigl(\lambda^{SA} \bar\beta + \eta - \lambda^{AI} A_t\bigr)$, so $A_t$ increases toward $\bar a$ from below when $\bar a \le 1$, and toward $1$ when $\bar a > 1$ (then $\dot A_t > 0$ on $[0,1)$); with $\lambda^{AR} > 0$ the extra outflow keeps $A_t$ strictly below $\bar a$. For the threshold policy the HJB is linear in $u$, so the optimal control is bang-bang with switching function $\mathcal{M}_t(\cdot, a)$; the proof analyzes the sign of this function along the one-dimensional belief and shows a single sign change when symptom onset is fast enough, and compares it with the belief ceiling to locate $a^{\mathrm{thresh}}$ above $\lambda^{SA} \bar\beta / \lambda^{AI}$.

## Sources

- S. Yagiz Olmez, Shubham Aggarwal, Jin Won Kim, Erik Miehling, Tamer Basar, Matthew West et al., "How does a Rational Agent Act in an Epidemic?", in 2022 IEEE 61st Conference on Decision and Control (CDC) (2022), 5536–5543, <https://doi.org/10.1109/cdc51059.2022.9992844>. Published version of arXiv:2206.02222, cited next; locators there refer to the arXiv version.
- S. Yagiz Olmez, Shubham Aggarwal, Jin Won Kim, Erik Miehling, Tamer Başar, Matthew West, Prashant G. Mehta, "How does a Rational Agent Act in an Epidemic?", arXiv (2022). Propositions 2, 4 and 5, Section 3 (nonlinear filter) and Section 4. <https://doi.org/10.48550/arXiv.2206.02222>
