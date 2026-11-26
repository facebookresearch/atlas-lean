# Estimation-to-decisions meta-algorithm

In the **decision making with structured observations** framework, a model class $\mathcal{M}$ consists of models $M$ mapping each decision $\pi \in \Pi$ to a distribution $M(\pi)$ over pairs $(r, o)$ of a reward $r \in [0,1]$ and an observation $o \in \mathcal{O}$; $f^M(\pi) = \mathbb{E}^{M,\pi}[r]$ is the mean reward and $\pi_M \in \arg\max_\pi f^M(\pi)$ an optimal decision. Over $T$ rounds a learner chooses $\pi_t$ (possibly at random) using past data and observes $(r_t, o_t) \sim M^\star(\pi_t)$ for an unknown $M^\star \in \mathcal{M}$; its regret is $\mathrm{Reg}_T = \sum_{t=1}^T \big(f^{M^\star}(\pi_{M^\star}) - f^{M^\star}(\pi_t)\big)$. Bandits (observations empty), contextual bandits and episodic reinforcement learning (observations are trajectories, decisions are policies) are special cases. An **online estimation oracle** outputs at each round $t$ an estimate $\hat M_t$ (possibly outside $\mathcal{M}$) from the history, and its **Hellinger estimation error** is $\mathrm{Est}_H = \sum_{t=1}^T \mathbb{E}_{\pi_t \sim p_t}\big[D_H^2(M^\star(\pi_t), \hat M_t(\pi_t))\big]$. The **Estimation-to-Decisions** (E2D) algorithm with parameter $\gamma$ computes at each round

$$
p_t \in \arg\min_{p \in \Delta(\Pi)} \sup_{M \in \mathcal{M}} \mathbb{E}_{\pi \sim p}\Big[f^M(\pi_M) - f^M(\pi) - \gamma D_H^2\big(M(\pi), \hat M_t(\pi)\big)\Big],
$$

samples $\pi_t \sim p_t$, observes $(r_t, o_t)$ and updates the oracle.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)

## Sources

- D. J. Foster, S. M. Kakade, J. Qian, A. Rakhlin, "The Statistical Complexity of Interactive Decision Making", arXiv:2112.13487 (2021).
