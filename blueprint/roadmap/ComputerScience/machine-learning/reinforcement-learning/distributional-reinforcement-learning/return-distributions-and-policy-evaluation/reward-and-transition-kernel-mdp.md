# Finite MDP with a joint reward and next-state kernel

A finite Markov decision process for distributional reinforcement learning draws the immediate reward and the next state jointly: every state–action pair carries a probability law on $\mathbb{R} \times \mathcal{X}$, so the reward is random and may depend on the next state.

Let $\mathcal{X}$ and $\mathcal{A}$ be finite nonempty sets of states and actions and let $\gamma \in [0,1)$ be the discount factor. A *reward–transition kernel* assigns to each $(x,a) \in \mathcal{X} \times \mathcal{A}$ a probability measure $\mathsf{p}(\cdot \mid x,a)$ on $\mathbb{R} \times \mathcal{X}$, with the Borel sets on $\mathbb{R}$ and all subsets of $\mathcal{X}$. For a Borel set $B \subseteq \mathbb{R}$ write

$$\mathsf{p}(B, x' \mid x,a) = \mathsf{p}(B \times \{x'\} \mid x,a), \qquad P(x' \mid x,a) = \mathsf{p}(\mathbb{R}, x' \mid x,a).$$

Each $\mathsf{p}(\cdot, x' \mid x,a)$ is a finite measure on $\mathbb{R}$ of total mass $P(x' \mid x,a)$, and the numbers $P(x' \mid x,a)$ are the transition probabilities of a [stochastic Markov decision process](../../../../heuristic-search-and-planning/value-iteration/stochastic.md) on $\mathcal{X}$ and $\mathcal{A}$ with real entries. When $P(x' \mid x,a) > 0$, the conditional reward law given the next state is

$$\rho_{x,a,x'} = \frac{\mathsf{p}(\cdot, x' \mid x,a)}{P(x' \mid x,a)};$$

it is left undefined when $P(x' \mid x,a) = 0$, and no statement uses it there.

For $1 \le q < \infty$ the reward moment is

$$M_q = \max_{(x,a) \in \mathcal{X} \times \mathcal{A}} \Bigl( \int_{\mathbb{R} \times \mathcal{X}} |r|^q \, \mathsf{p}(dr, dx' \mid x,a) \Bigr)^{1/q} \in [0, \infty].$$

No moment condition is standing: a page that uses $M_1 < \infty$ or $M_q < \infty$ assumes it explicitly, and $M_q < \infty$ gives $M_1 \le M_q$ by Jensen's inequality. The Cramér-distance, projection, projected-operator and categorical evaluation pages need no moment condition; the categorical error bounds and categorical Q-learning assume $M_1 < \infty$. When $M_1 < \infty$, the mean reward is $\bar r(x,a) = \int r \, \mathsf{p}(dr, dx' \mid x,a)$; without that condition the integral may be undefined (for example for Cauchy rewards), and no page uses $\bar r$ without assuming $M_1 < \infty$.

**Product kernels.** Bellemare, Dabney and Munos model the reward $R(x,a)$ as a random variable independent of the next state, that is $\mathsf{p}(\cdot \mid x,a) = R(x,a) \otimes P(\cdot \mid x,a)$, so that $\rho_{x,a,x'}$ is the law of $R(x,a)$ for every $x'$ with $P(x' \mid x,a) > 0$. That is a special case: a joint kernel whose reward law depends on the next state is not a product kernel, and the pages of this topic never replace one by the other. Results stated for joint kernels cover product kernels, and every counterexample in this setting uses a product kernel, so it is a counterexample for joint kernels too; the page on an optimality operator without a fixed point works instead in the source's undiscounted model with terminal actions. The two pages on means of distributional updates state the source's product-kernel identities; their joint-kernel computation is a remark in their expansions.

Policies are [stochastic policies](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md) $\pi(\cdot \mid x)$ on $\mathcal{A}$.

## Depends on

- [Stochastic Markov decision process](../../../../heuristic-search-and-planning/value-iteration/stochastic.md)
- [Probability measure](../../../../../Probability/foundations/probability-measures/is-probability-measure.md)

## Proof depends on

None.

## Expansion

Rowland, Bellemare, Dabney, Munos and Teh work with exactly this object: a joint kernel $\mathsf{p} : \mathcal{X} \times \mathcal{A} \to \mathscr{P}(\mathbb{R} \times \mathcal{X})$ on finite $\mathcal{X}$ and $\mathcal{A}$ with $\gamma \in [0,1)$. Bellemare, Dabney and Munos allow general state spaces and $\gamma \in [0,1]$ and write that the reward, the transition and the next-state value are independent. Read literally that cannot hold in general, since the next-state value is selected by the successor; the intended model, used throughout this topic, draws the reward independently of the successor and then draws the next return freshly, conditionally on the selected successor and action. The topic keeps finite spaces and $\gamma < 1$, which every fixed-point and convergence statement needs. Bellemare, Dabney and Munos work in a space of value distributions with bounded moments (their Section 3.2) and take the reward vector in that space (Section 3.3); Rowland and coauthors name no moment condition. $M_1$ and $M_q$ make explicit what the return distribution and the Wasserstein results use. The conditional laws $\rho_{x,a,x'}$ exist because $\mathcal{X}$ is finite, so no disintegration theorem is needed.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 2.1 (joint kernel on finite state and action spaces) and Section 2.2 ($\gamma \in [0,1)$).
- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 2 (the MDP $(\mathcal{X}, \mathcal{A}, R, P, \gamma)$ with random reward) and Section 3.3 (independence of reward, transition and next-state return).
