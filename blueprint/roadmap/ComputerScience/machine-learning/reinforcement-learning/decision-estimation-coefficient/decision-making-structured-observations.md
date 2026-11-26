# Decision making with structured observations

In the **decision making with structured observations** framework, a model class $\mathcal{M}$ consists of models $M$ mapping each decision $\pi \in \Pi$ to a distribution $M(\pi)$ over pairs $(r, o)$ of a reward $r \in [0,1]$ and an observation $o \in \mathcal{O}$; $f^M(\pi) = \mathbb{E}^{M,\pi}[r]$ is the mean reward and $\pi_M \in \arg\max_\pi f^M(\pi)$ an optimal decision. Over $T$ rounds a learner chooses $\pi_t$ (possibly at random) using past data and observes $(r_t, o_t) \sim M^\star(\pi_t)$ for an unknown $M^\star \in \mathcal{M}$; its regret is $\mathrm{Reg}_T = \sum_{t=1}^T \big(f^{M^\star}(\pi_{M^\star}) - f^{M^\star}(\pi_t)\big)$. Bandits (observations empty), contextual bandits and episodic reinforcement learning (observations are trajectories, decisions are policies) are special cases.

## Depends on

- [Stochastic k-armed bandits: canonical history law and regret](../multi-armed-bandits/stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Sources

- D. J. Foster, S. M. Kakade, J. Qian, A. Rakhlin, "The Statistical Complexity of Interactive Decision Making", arXiv:2112.13487 (2021).
