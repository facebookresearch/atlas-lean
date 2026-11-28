# The return distribution has finite moments

If the rewards have finite $q$-th moments, so do the returns of every policy, with norm at most $M_q / (1 - \gamma)$.

Let $1 \le q < \infty$, let $\mathsf{p}$ be a [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) with $M_q < \infty$, $\gamma \in [0,1)$ and $\pi$ a stochastic policy. Then the [return distribution](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md) satisfies $\eta_\pi \in \mathscr{P}_q(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ (notation of [return-distribution functions](../return-distributions-and-policy-evaluation/return-distribution-function.md)), and for every $(x,a)$

$$\Bigl( \int_{\mathbb{R}} |t|^q \, \eta_\pi^{(x,a)}(dt) \Bigr)^{1/q} \le \frac{M_q}{1 - \gamma}.$$

## Depends on

- [Return distribution of a policy](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md)
- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)

## Proof depends on

- [Return distribution of a policy](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)
- [Markov property of the canonical Markov chain measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-cond-distrib.md)
- [Initial distribution of the canonical Markov chain measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-initial-distributio.md)

## Expansion

Under $\mathbb{P}_{x,a}$, the conditional law of $\omega_{t+1}$ given the past is $\kappa(\omega_t, \cdot)$ ([Markov property of the canonical measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-cond-distrib.md), with the Dirac [initial distribution](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-initial-distributio.md)), so conditioning on $(X_t, A_t)$ gives $\mathbb{E} |R_t|^q \le M_q^q$, so $\|R_t\|_{L^q} \le M_q$. Minkowski's inequality gives $\| \sum_{t < n} \gamma^t |R_t| \|_{L^q} \le \sum_{t < n} \gamma^t M_q \le M_q/(1-\gamma)$, and monotone convergence passes to $n \to \infty$. Since $|G| \le \sum_t \gamma^t |R_t|$ almost surely, $\|G\|_{L^q} \le M_q/(1-\gamma)$, which is the claim because $\eta_\pi^{(x,a)}$ is the law of $G$. Boundary cases: $\gamma = 0$ gives $G = R_0$ and the bound $M_q$; $M_q = 0$ means that every reward is zero almost surely and $\eta_\pi^{(x,a)} = \delta_0$.

Bellemare, Dabney and Munos assume that $Z^\pi$ lies in their space of value distributions with bounded moments and do not derive it; this page derives the moment bound from the reward moments, which is what the convergence of distributional Bellman iterates needs.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.2 (the space of value distributions with bounded moments) and Section 3.3.1, paragraph after Lemma 3 ("As we assume all moments are bounded").
