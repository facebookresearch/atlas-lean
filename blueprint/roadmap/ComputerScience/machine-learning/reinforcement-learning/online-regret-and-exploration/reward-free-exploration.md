# Reward-free exploration

In reward-free exploration a learner first explores an unknown episodic MDP for $K$ episodes without observing rewards, and afterwards, with no further interaction, must return an $\varepsilon$-optimal policy for every reward function it is then given, however many and however chosen.

Let $M$ be an [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) with $S$ states, $A$ actions, horizon $H$, stage-dependent transition kernels $P_h$ and an initial distribution $P_1$ of $s_1$, all unknown. Policies $\pi = (\pi_h)_{h \le H}$ may be stochastic, $\pi_h : \mathcal{S} \to \Delta(\mathcal{A})$. The protocol has two phases.

1. Exploration phase: for $k = 1, \dots, K$ the learner picks a policy, $s_1 \sim P_1$ is drawn, and for $h = 1, \dots, H$ the learner draws $a_h \sim \pi_h(\cdot \mid s_h)$ and observes $s_{h+1} \sim P_h(\cdot \mid s_h, a_h)$. No reward is revealed. The result is a dataset $\mathcal{D}$ of the visited states and actions.
2. Planning phase: the learner may no longer interact with $M$. It receives reward functions $r = (r_h)_{h \le H}$ with $r_h : \mathcal{S} \times \mathcal{A} \to [0, 1]$, possibly adversarially and adaptively chosen, and for each returns a policy $\pi$ computed from $\mathcal{D}$ and $r$.

Writing $V_1^\pi(\cdot\,; r)$ and $V_1^\star(\cdot\,; r)$ for the values under reward $r$, the learner succeeds if every returned policy is $\varepsilon$-optimal for its reward,

$$
\mathbb{E}_{s_1 \sim P_1}\big[V_1^\star(s_1; r) - V_1^\pi(s_1; r)\big] \le \varepsilon,
$$

and its sample complexity is the number $K$ of exploration episodes needed to succeed with probability at least $1 - p$.

For $\delta > 0$, a state $s$ is $\delta$-significant at step $h$ if some policy reaches it at step $h$ with probability at least $\delta$: $\max_\pi P_h^\pi(s) \ge \delta$.

## Depends on

- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)
- [Online episodic learning and regret](online-episodic-learning-and-regret.md)

## Proof depends on

None.

## Expansion

Supplying the reward after exploration makes the problem harder than ordinary episodic learning, so a reward-free algorithm also solves the setting in which rewards are observed during exploration. A state that is not $\delta$-significant for small $\delta$ is rarely reached by any policy and so changes values from the initial distribution little, which is why exploring the significant states suffices. Jin, Krishnamurthy, Simchowitz and Yu motivate the setting by batch reinforcement learning: the exploration phase produces a dataset with good coverage, on which any planner can then be run.

## Sources

- C. Jin, A. Krishnamurthy, M. Simchowitz and T. Yu, "Reward-Free Exploration for Reinforcement Learning", *Proceedings of the 37th International Conference on Machine Learning* (ICML 2020), PMLR 119, Section 2 (episodic MDP, the $\varepsilon$-optimality criterion, Protocol 1 and the description of the exploration and planning phases) and Definition 3.2 ($\delta$-significant states). [PDF](https://proceedings.mlr.press/v119/jin20d/jin20d.pdf)
