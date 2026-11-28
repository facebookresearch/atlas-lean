# Contextual bandits with online regression oracles

In a **contextual bandit** with $K$ actions, at each round $t$ the environment reveals a context $x_t$ (possibly adversarially), the learner chooses an action $a_t$ and observes a reward $r_t \in [0,1]$ with $\mathbb{E}[r_t \mid x_t, a_t] = f^\star(x_t, a_t)$ for an unknown $f^\star \in \mathcal{F}$ (realizability). An **online regression oracle** for $\mathcal{F}$ receives the pairs $((x_t, a_t), r_t)$ sequentially and outputs predictors $\hat f_t$ before each round, with square-loss regret $\mathrm{Reg}_{\mathrm{Sq}}(T)$ such that $\sum_t (\hat f_t(x_t, a_t) - r_t)^2 - \inf_{f \in \mathcal{F}}\sum_t (f(x_t,a_t) - r_t)^2 \le \mathrm{Reg}_{\mathrm{Sq}}(T)$ for every sequence.

## Depends on

- [Stochastic k-armed bandits: canonical history law](../multi-armed-bandits/stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [Decision making with structured observations](../decision-estimation-coefficient/decision-making-structured-observations.md)

## Sources

- D. J. Foster, A. Rakhlin, "Beyond UCB: Optimal and Efficient Contextual Bandits with Regression Oracles", ICML (2020), arXiv:2002.04926, Section 2 (Assumptions 1 and 2a).
