# Return distribution of a policy

The return distribution of a policy $\pi$ at $(x,a)$ is the law of the discounted sum of rewards $\sum_t \gamma^t R_t$ along the trajectory that starts in state $x$ with action $a$ and then follows $\pi$.

Fix a [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) $\mathsf{p}$ with $M_1 < \infty$, a discount $\gamma \in [0,1)$ and a [stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md) $\pi$. On $S = \mathcal{X} \times \mathcal{A} \times \mathbb{R}$, with the discrete $\sigma$-algebras on the finite sets $\mathcal{X}$ and $\mathcal{A}$ and the Borel sets on $\mathbb{R}$ (a nonempty standard Borel space), let $\kappa$ be the Markov kernel

$$\kappa\bigl((x,a,s), \{x'\} \times \{a'\} \times B\bigr) = \mathsf{p}(B, x' \mid x,a) \, \pi(a' \mid x'),$$

which ignores the last coordinate $s$ of the current state; it is measurable because it factors through the projection to the finite set $\mathcal{X} \times \mathcal{A}$, and each $\kappa(y, \cdot)$ is a probability measure. For $(x,a) \in \mathcal{X} \times \mathcal{A}$ let $\mathbb{P}_{x,a}$ be the [Markov chain path measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-path-measure.md) on $S^{\mathbb{N}}$ of $\kappa$ with initial law the Dirac mass at $(x,a,0)$, and write the coordinates of a path as $\omega_t = (X_t, A_t, R_{t-1})$, so that $(X_0, A_0) = (x,a)$, the pair $(R_t, X_{t+1})$ has law $\mathsf{p}(\cdot \mid X_t, A_t)$ given the past, and $A_{t+1}$ has law $\pi(\cdot \mid X_{t+1})$ given the past and $(R_t, X_{t+1})$. The return is

$$G(\omega) = \sum_{t \ge 0} \gamma^t R_t(\omega)$$

where the series is absolutely summable, and $G(\omega) = 0$ elsewhere. The *return distribution* of $\pi$ is the [return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)

$$\eta_\pi^{(x,a)} = \text{law of } G \text{ under } \mathbb{P}_{x,a}, \qquad (x,a) \in \mathcal{X} \times \mathcal{A}.$$

Under $M_1 < \infty$ the series is absolutely summable $\mathbb{P}_{x,a}$-almost surely, so the convention off that event does not affect $\eta_\pi$. Each $\eta_\pi^{(x,a)}$ is defined by starting the chain at $(x,a)$, so no conditioning on an event $\{X_0 = x, A_0 = a\}$ of possibly zero probability is involved, and pairs that $\pi$ never visits from a given start still have a return distribution.

## Depends on

- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)
- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)
- [Stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)
- [Markov chain path measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-path-measure.md)

## Proof depends on

- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)
- [Markov chain path measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-path-measure.md)
- [Initial distribution of the canonical Markov chain measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-initial-distributio.md)
- [Markov property of the canonical Markov chain measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-cond-distrib.md)

## Expansion

Under $\mathbb{P}_{x,a}$ the law of $\omega_0$ is the Dirac mass at $(x,a,0)$ ([initial distribution](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-initial-distributio.md)), and the conditional law of $\omega_{t+1}$ given $(\omega_0, \dots, \omega_t)$ is $\kappa(\omega_t, \cdot)$ ([Markov property of the canonical measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-cond-distrib.md)); the path measure is that canonical Markov chain measure. Conditionally on $(X_t, A_t)$, the reward $R_t$, read off $\omega_{t+1}$, therefore has the reward marginal of $\mathsf{p}(\cdot \mid X_t, A_t)$, so $\mathbb{E}_{x,a} |R_t| \le M_1$ for every $t$ by the tower property. By monotone convergence $\mathbb{E}_{x,a} \sum_t \gamma^t |R_t| \le M_1 / (1 - \gamma) < \infty$, hence the series is absolutely summable almost surely. The set where it is absolutely summable is measurable and $G$ is a pointwise limit of measurable functions there, so its law is a Borel probability measure. Rowland and coauthors write $\eta_\pi^{(x,a)} = \mathrm{Law}_\pi(\sum_t \gamma^t R_t \mid X_0 = x, A_0 = a)$; starting the chain at $(x,a)$ is the construction that this conditional notation stands for. The extra coordinate carries the reward, which in a joint kernel is drawn together with the next state; the chain on $S$ makes that draw a single Markov step.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 2.1 (the process $(X_t, A_t, R_t)$) and Section 2.2, eqs. (1)–(2).
- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 2.1, eq. (1) (the return $Z^\pi$ with $Q^\pi = \mathbb{E} Z^\pi$).
