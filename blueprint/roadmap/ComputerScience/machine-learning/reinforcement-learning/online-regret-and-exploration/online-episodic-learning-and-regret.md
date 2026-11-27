# Online episodic learning and regret

In online episodic reinforcement learning a learner plays $K$ episodes of length $H$ in an unknown episodic MDP, choosing each episode's policy from the data of earlier episodes. Its regret is the sum over episodes of the gap between the optimal value and the value of the policy it played, both from that episode's initial state.

Let $M$ be an [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) whose state set, action set and horizon $H$ are known to the learner and whose transition kernels are unknown. In episode $k = 1, \dots, K$:

1. an initial state $x_1^k$ is given, either chosen arbitrarily by an adversary (the adversarial-start protocol) or drawn independently from a fixed unknown distribution $\mu$ on $\mathcal{S}$ (the stochastic-start protocol);
2. the learner chooses a policy $\pi_k$ as a function of everything observed in episodes $1, \dots, k-1$ and of $x_1^k$, possibly with internal randomization;
3. the learner plays $\pi_k$ for $H$ steps, observing $x_h^k$, the action $a_h^k$, the reward and the next state $x_{h+1}^k \sim P_h(\cdot \mid x_h^k, a_h^k)$ for $h = 1, \dots, H$.

The regret after $K$ episodes is the random variable

$$
\mathrm{Regret}(K) = \sum_{k=1}^{K} \big(V_1^\star(x_1^k) - V_1^{\pi_k}(x_1^k)\big),
$$

where $V_1^\star$ and $V_1^{\pi_k}$ are values in the true MDP $M$. Each summand lies in $[0, H]$ when rewards lie in $[0, 1]$, so $0 \le \mathrm{Regret}(K) \le HK$. The total number of steps is $T = KH$.

In the stochastic-start protocol a policy $\hat\pi$ is $\varepsilon$-optimal if $\mathbb{E}_{x_1 \sim \mu}[V_1^\star(x_1) - V_1^{\hat\pi}(x_1)] \le \varepsilon$, and the sample complexity of a learner that outputs such a policy with probability at least $1 - \delta$ is the number of episodes it uses.

## Depends on

- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)

## Proof depends on

None.

## Expansion

Upper bounds in this literature hold with high probability for the random quantity $\mathrm{Regret}(K)$; lower bounds are usually for its expectation. Domingues, Ménard, Kaufmann and Valko define the expected regret after $T$ episodes as $\mathbb{E}\big[\sum_{t=1}^{T} (\rho^\star - \rho^{\pi,t})\big]$, with $\rho^\star$ the optimal value averaged over $\mu$, so their $T$ counts episodes, while Jin, Allen-Zhu, Bubeck and Jordan and Azar, Osband and Munos write $T = KH$ for steps. A leading term $\sqrt{H^2 S A T}$ with $T$ steps is $\sqrt{H^3 S A K}$ with $K$ episodes. Sample complexities are likewise stated in episodes; Zhang, Chen, Lee and Du note that $SAH^3/\varepsilon^2$ episodes are $SAH^4/\varepsilon^2$ transitions.

Regret and sample complexity are related by an online-to-batch argument. Jin, Allen-Zhu, Bubeck and Jordan observe that, with a fixed start $x_1$, a regret of at most $C T^{1-\alpha}$ makes the policy $\pi_k$ of a uniformly random episode $k$ satisfy $V_1^\star(x_1) - V_1^{\pi_k}(x_1) \le 3CH T^{-\alpha}$ with probability at least $2/3$ by Markov's inequality, since the average gap is at most $C T^{1-\alpha} / K$. Conversely, an $\varepsilon$-optimal policy found with few samples and then played gives regret sublinear in $T$ against a stochastic start. The stochastic-bandit regret of [stochastic k-armed bandits](../multi-armed-bandits/stochastic-k-armed-bandits-canonical-history-law-and-regret.md) is the case $H = 1$ with a single state, up to the convention that bandit rewards are random.

## Sources

- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", *Advances in Neural Information Processing Systems 31* (NeurIPS 2018), Section 2 (the protocol with adversarial initial states and $\mathrm{Regret}(K)$) and Table 1 ($T = KH$). [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf); full version arXiv:1807.03765v1, Section 3.1 (from regret to PAC guarantees).
- M. G. Azar, I. Osband and R. Munos, "Minimax Regret Bounds for Reinforcement Learning", ICML 2017, PMLR 70, Section 2 (regret over $T = KH$ steps, initial states chosen by the environment); arXiv:1703.05449v2. [PDF](https://proceedings.mlr.press/v70/azar17a/azar17a.pdf)
- O. D. Domingues, P. Ménard, E. Kaufmann and M. Valko, "Episodic Reinforcement Learning in Finite MDPs: Minimax Lower Bounds Revisited", ALT 2021, PMLR 132, Section 2, Definitions 1 to 3 (expected regret after $T$ episodes, PAC exploration, best-policy identification). [PDF](https://proceedings.mlr.press/v132/domingues21a/domingues21a.pdf)
- Z. Zhang, Y. Chen, J. D. Lee and S. S. Du, "Settling the Sample Complexity of Online Reinforcement Learning", arXiv:2307.13586v4, Section 2 (data collection protocol with $x_1^k \sim \mu$, the regret (17) and the $\varepsilon$-optimality criterion); COLT 2024, PMLR 247; *Journal of the ACM* (2025), doi:10.1145/3733592.
