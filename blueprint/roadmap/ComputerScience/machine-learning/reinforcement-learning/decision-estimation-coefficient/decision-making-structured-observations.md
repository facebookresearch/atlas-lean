# Decision making with structured observations

In the **decision making with structured observations** framework, a model class $\mathcal{M}$ consists of models $M$ mapping each decision $\pi \in \Pi$ to a distribution $M(\pi)$ over pairs $(r, o)$ of a real reward $r$ and an observation $o \in \mathcal{O}$; $f^M(\pi) = \mathbb{E}^{M,\pi}[r]$ is the mean reward, assumed to lie in $[0,1]$ (only the mean is bounded: the draws themselves may be unbounded, as for Gaussian rewards $M(\pi) = \mathcal{N}(f(\pi), 1)$) and $\pi_M \in \arg\max_\pi f^M(\pi)$ an optimal decision. Over $T$ rounds a learner draws $\pi_t$ from a distribution $p_t$ chosen using past data and observes $(r_t, o_t) \sim M^\star(\pi_t)$ for an unknown $M^\star \in \mathcal{M}$ (realizability); its regret is $\mathrm{Reg}_T = \sum_{t=1}^T \mathbb{E}_{\pi_t \sim p_t}\big[f^{M^\star}(\pi_{M^\star}) - f^{M^\star}(\pi_t)\big]$. Bandits (observations empty), contextual bandits with i.i.d. contexts (contexts are observations, decisions map contexts to actions) and episodic reinforcement learning (observations are trajectories, decisions are policies) are special cases.

## Depends on

- [Stochastic k-armed bandits: canonical history law](../multi-armed-bandits/stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Sources

- D. J. Foster, A. Rakhlin, "Foundations of Reinforcement Learning and Interactive Decision Making", lecture notes, revised edition (September 2026), arXiv:2312.16730v2, Section 7.1 (Assumptions 7.1 and 7.2, the bounded-mean convention after them, Eq. (7.3), Examples 7.1–7.3) and Example 7.4.
- D. J. Foster, N. Golowich, Y. Han, "Tight Guarantees for Interactive Decision Making with the Decision-Estimation Coefficient", COLT (2023), PMLR 195, Section 1.1, Eq. (1).
