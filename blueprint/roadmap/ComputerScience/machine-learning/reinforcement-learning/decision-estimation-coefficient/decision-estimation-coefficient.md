# Decision-estimation coefficient

In the **decision making with structured observations** framework, a model class $\mathcal{M}$ consists of models $M$ mapping each decision $\pi \in \Pi$ to a distribution $M(\pi)$ over pairs $(r, o)$ of a real reward $r$ and an observation $o \in \mathcal{O}$; $f^M(\pi) = \mathbb{E}^{M,\pi}[r]$ is the mean reward, assumed to lie in $[0,1]$ (only the mean is bounded: the draws themselves may be unbounded, as for Gaussian rewards $M(\pi) = \mathcal{N}(f(\pi), 1)$) and $\pi_M \in \arg\max_\pi f^M(\pi)$ an optimal decision. Over $T$ rounds a learner draws $\pi_t$ from a distribution $p_t$ chosen using past data and observes $(r_t, o_t) \sim M^\star(\pi_t)$ for an unknown $M^\star \in \mathcal{M}$ (realizability); its regret is $\mathrm{Reg}_T = \sum_{t=1}^T \mathbb{E}_{\pi_t \sim p_t}\big[f^{M^\star}(\pi_{M^\star}) - f^{M^\star}(\pi_t)\big]$. Bandits (observations empty), contextual bandits with i.i.d. contexts (contexts are observations, decisions map contexts to actions) and episodic reinforcement learning (observations are trajectories, decisions are policies) are special cases. For $\gamma > 0$ and a reference model $\bar M$, the **decision-estimation coefficient** (DEC) is

$$
\mathrm{dec}_\gamma(\mathcal{M}, \bar M) = \inf_{p \in \Delta(\Pi)} \sup_{M \in \mathcal{M}} \mathbb{E}_{\pi \sim p}\Big[ f^M(\pi_M) - f^M(\pi) - \gamma\, D_H^2\big(M(\pi), \bar M(\pi)\big) \Big],
$$

where $D_H^2(P, Q) = \int \big(\sqrt{dP/d\nu} - \sqrt{dQ/d\nu}\big)^2\, d\nu = 2\, d_{\mathrm{Hell}}(P, Q)^2$ is the unnormalized squared Hellinger distance, twice the square of the linked Hellinger distance $d_{\mathrm{Hell}}$, and $\mathrm{dec}_\gamma(\mathcal{M}) = \sup_{\bar M \in \mathrm{co}(\mathcal{M})} \mathrm{dec}_\gamma(\mathcal{M}, \bar M)$, where $\mathrm{co}(\mathcal{M})$ is the set of mixtures of models in $\mathcal{M}$. The DEC is the value of a game in which the learner picks a distribution over decisions to trade off regret against information (measured by how much any alternative model differs from the reference model on the chosen decisions).

## Depends on

- [Decision making with structured observations](decision-making-structured-observations.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- D. J. Foster, A. Rakhlin, "Foundations of Reinforcement Learning and Interactive Decision Making", lecture notes, revised edition (September 2026), arXiv:2312.16730v2, Section 7.3, Eqs. (7.10)–(7.11).
- D. J. Foster, N. Golowich, Y. Han, "Tight Guarantees for Interactive Decision Making with the Decision-Estimation Coefficient", COLT (2023), PMLR 195, Section 1.2, Eq. (4).
