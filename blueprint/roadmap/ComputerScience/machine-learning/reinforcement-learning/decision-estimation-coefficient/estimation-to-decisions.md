# Estimation-to-decisions meta-algorithm

In the **decision making with structured observations** framework, a model class $\mathcal{M}$ consists of models $M$ mapping each decision $\pi \in \Pi$ to a distribution $M(\pi)$ over pairs $(r, o)$ of a real reward $r$ and an observation $o \in \mathcal{O}$; $f^M(\pi) = \mathbb{E}^{M,\pi}[r]$ is the mean reward, assumed to lie in $[0,1]$ (only the mean is bounded: the draws themselves may be unbounded, as for Gaussian rewards $M(\pi) = \mathcal{N}(f(\pi), 1)$) and $\pi_M \in \arg\max_\pi f^M(\pi)$ an optimal decision. Over $T$ rounds a learner draws $\pi_t$ from a distribution $p_t$ chosen using past data and observes $(r_t, o_t) \sim M^\star(\pi_t)$ for an unknown $M^\star \in \mathcal{M}$ (realizability); its regret is $\mathrm{Reg}_T = \sum_{t=1}^T \mathbb{E}_{\pi_t \sim p_t}\big[f^{M^\star}(\pi_{M^\star}) - f^{M^\star}(\pi_t)\big]$. Bandits (observations empty), contextual bandits with i.i.d. contexts (contexts are observations, decisions map contexts to actions) and episodic reinforcement learning (observations are trajectories, decisions are policies) are special cases. An **online estimation oracle** outputs at each round $t$ an estimate $\hat M_t \in \widehat{\mathcal{M}}$ from the history, where $\widehat{\mathcal{M}} \supseteq \mathcal{M}$ is a fixed class of models (so estimates may lie outside $\mathcal{M}$), and its **Hellinger estimation error** is $\mathrm{Est}_H = \sum_{t=1}^T \mathbb{E}_{\pi_t \sim p_t}\big[D_H^2(M^\star(\pi_t), \hat M_t(\pi_t))\big]$, with $D_H^2(P, Q) = \int \big(\sqrt{dP/d\nu} - \sqrt{dQ/d\nu}\big)^2\, d\nu = 2\, d_{\mathrm{Hell}}(P, Q)^2$ the unnormalized squared Hellinger distance of the DEC. The **Estimation-to-Decisions** (E2D) algorithm with parameter $\gamma$ computes at each round

$$
p_t \in \arg\min_{p \in \Delta(\Pi)} \sup_{M \in \mathcal{M}} \mathbb{E}_{\pi \sim p}\Big[f^M(\pi_M) - f^M(\pi) - \gamma D_H^2\big(M(\pi), \hat M_t(\pi)\big)\Big],
$$

samples $\pi_t \sim p_t$, observes $(r_t, o_t)$ and updates the oracle.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- D. J. Foster, A. Rakhlin, "Foundations of Reinforcement Learning and Interactive Decision Making", lecture notes, revised edition (September 2026), arXiv:2312.16730v2, Section 7.4 (Definition 7.1 and Algorithm 7.1).
