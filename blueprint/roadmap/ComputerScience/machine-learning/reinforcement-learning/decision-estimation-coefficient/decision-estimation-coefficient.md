# Decision-estimation coefficient

In the **decision making with structured observations** framework, a model class $\mathcal{M}$ consists of models $M$ mapping each decision $\pi \in \Pi$ to a distribution $M(\pi)$ over pairs $(r, o)$ of a reward $r \in [0,1]$ and an observation $o \in \mathcal{O}$; $f^M(\pi) = \mathbb{E}^{M,\pi}[r]$ is the mean reward and $\pi_M \in \arg\max_\pi f^M(\pi)$ an optimal decision. Over $T$ rounds a learner chooses $\pi_t$ (possibly at random) using past data and observes $(r_t, o_t) \sim M^\star(\pi_t)$ for an unknown $M^\star \in \mathcal{M}$; its regret is $\mathrm{Reg}_T = \sum_{t=1}^T \big(f^{M^\star}(\pi_{M^\star}) - f^{M^\star}(\pi_t)\big)$. Bandits (observations empty), contextual bandits and episodic reinforcement learning (observations are trajectories, decisions are policies) are special cases. For $\gamma > 0$ and a reference model $\bar M$, the **decision-estimation coefficient** (DEC) is

$$
\mathrm{dec}_\gamma(\mathcal{M}, \bar M) = \inf_{p \in \Delta(\Pi)} \sup_{M \in \mathcal{M}} \mathbb{E}_{\pi \sim p}\Big[ f^M(\pi_M) - f^M(\pi) - \gamma\, D_H^2\big(M(\pi), \bar M(\pi)\big) \Big],
$$

where $D_H^2$ is the squared Hellinger distance, and $\mathrm{dec}_\gamma(\mathcal{M}) = \sup_{\bar M \in \mathcal{M}} \mathrm{dec}_\gamma(\mathcal{M}, \bar M)$. The DEC is the value of a game in which the learner picks a distribution over decisions to trade off regret against information (measured by how much any alternative model differs from the reference model on the chosen decisions). The **localized** version $\mathrm{dec}_{\gamma,\varepsilon}$ restricts the supremum to models $M$ with $f^M(\pi_M) \le f^{\bar M}(\pi_{\bar M}) + \varepsilon$.

## Depends on

- [Decision making with structured observations](decision-making-structured-observations.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- D. J. Foster, S. M. Kakade, J. Qian, A. Rakhlin, "The Statistical Complexity of Interactive Decision Making", arXiv:2112.13487 (2021).
