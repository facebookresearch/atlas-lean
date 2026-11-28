# The return distribution solves the distributional Bellman equation

The return distribution of a policy is a fixed point of its distributional Bellman operator: $\eta_\pi = \mathcal{T}^\pi \eta_\pi$.

Let $\mathsf{p}$ be a reward–transition kernel with $M_1 < \infty$, $\gamma \in [0,1)$ and $\pi$ a stochastic policy. Then the [return distribution](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md) $\eta_\pi$ and the [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md) satisfy, for every $(x,a) \in \mathcal{X} \times \mathcal{A}$,

$$\eta_\pi^{(x,a)} = \sum_{(x',a') \in \mathcal{X} \times \mathcal{A}} \pi(a' \mid x') \int_{\mathbb{R}} (f_{r,\gamma})_\# \eta_\pi^{(x',a')} \, \mathsf{p}(dr, x' \mid x,a).$$

## Depends on

- [Return distribution of a policy](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)

## Proof depends on

- [Return distribution of a policy](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Markov chain path measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-path-measure.md)
- [Markov property, set-integral form](../../../../../Probability/markov-chains/markov-and-strong-markov-properties/markov-set-integral-shift.md)
- [Markov property of the canonical Markov chain measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-cond-distrib.md)
- [Initial distribution of the canonical Markov chain measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-initial-distributio.md)

## Expansion

Work under $\mathbb{P}_{x,a}$, the path measure of the chain $\omega_t = (X_t, A_t, R_{t-1})$ on the nonempty standard Borel space $S = \mathcal{X} \times \mathcal{A} \times \mathbb{R}$, started at $(x,a,0)$. On the almost sure event where the series is absolutely summable, $G = R_0 + \gamma \, G \circ \theta_1$, where $\theta_1$ is the time shift and $R_0$ is the last coordinate of $\omega_1$.

The [set-integral form of the Markov property](../../../../../Probability/markov-chains/markov-and-strong-markov-properties/markov-set-integral-shift.md) at time $1$, applied to $A = \{\omega_1 \in D\}$ and $Y = \mathbf{1}_C$, gives $\mathbb{P}_{x,a}(\omega_1 \in D, \theta_1 \omega \in C) = \int_{\{\omega_1 \in D\}} \mathbb{P}_{\omega_1}(C) \, d\mathbb{P}_{x,a}$ for measurable $D \subseteq S$ and $C \subseteq S^{\mathbb{N}}$, where $\mathbb{P}_y$ is the chain started at $y$. Under $\mathbb{P}_{x,a}$ the law of $\omega_1$ is $\kappa((x,a,0), \cdot)$, by the Dirac [initial distribution](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-initial-distributio.md) and the [one-step conditional law](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-cond-distrib.md) at $n = 0$. By the π–λ theorem the joint law of $(\omega_1, \theta_1 \omega)$ is therefore $\int \delta_{y} \otimes \mathbb{P}_{y} \, \kappa((x,a,0), dy)$. Because $\kappa$ ignores the reward coordinate, the law of $G$ under $\mathbb{P}_{(x',a',r)}$ is $\eta_\pi^{(x',a')}$ for every $r$. Hence for Borel $B$,

$$\mathbb{P}_{x,a}(G \in B) = \sum_{(x',a')} \pi(a' \mid x') \int \eta_\pi^{(x',a')}(\{t : r + \gamma t \in B\}) \, \mathsf{p}(dr, x' \mid x,a) = (\mathcal{T}^\pi \eta_\pi)^{(x,a)}(B).$$

The equation is a property of the constructed law, so it needs no contraction or completeness argument. Bellemare, Dabney and Munos obtain it "by inspection" of the fixed point given by Banach's theorem; Rowland and coauthors restate it in pushforward form and credit it to them.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.3.1, paragraph after Lemma 3 (the fixed point "must be $Z^\pi$").
- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 2.3, the distributional Bellman equation stated before eq. (3).
