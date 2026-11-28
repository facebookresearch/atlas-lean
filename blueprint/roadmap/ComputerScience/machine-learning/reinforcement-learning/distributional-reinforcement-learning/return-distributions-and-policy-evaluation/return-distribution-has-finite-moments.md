# The return distribution has finite moments

If the rewards have finite $q$-th moments, so do the returns of every policy.

Let $1 \le q < \infty$, let $\mathsf{p}$ be a [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) with $M_q < \infty$, $\gamma \in [0,1)$ and $\pi$ a stochastic policy. Then the [return distribution](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md) satisfies $\eta_\pi \in \mathscr{P}_q(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ (notation of [return-distribution functions](../return-distributions-and-policy-evaluation/return-distribution-function.md)): $\int_{\mathbb{R}} |t|^q \, \eta_\pi^{(x,a)}(dt) < \infty$ for every $(x,a)$.

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

Under $\mathbb{P}_{x,a}$, the conditional law of $\omega_{t+1}$ given the past is $\kappa(\omega_t, \cdot)$ ([Markov property of the canonical measure](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-cond-distrib.md), with the Dirac [initial distribution](../../../../../Probability/markov-chains/construction-of-markov-chains/markov-chain-measure-initial-distributio.md)), so conditioning on $(X_t, A_t)$ gives $\mathbb{E} |R_t|^q \le M_q^q$, so $\|R_t\|_{L^q} \le M_q$. Minkowski's inequality gives $\| \sum_{t < n} \gamma^t |R_t| \|_{L^q} \le \sum_{t < n} \gamma^t M_q \le M_q/(1-\gamma)$, and monotone convergence passes to $n \to \infty$. Since $|G| \le \sum_t \gamma^t |R_t|$ almost surely, $\|G\|_{L^q} \le M_q/(1-\gamma)$, which gives the claim because $\eta_\pi^{(x,a)}$ is the law of $G$; the quantitative bound $M_q/(1-\gamma)$ is a by-product of this derivation and not part of the statement. Boundary cases: $\gamma = 0$ gives $G = R_0$; $M_q = 0$ means that every reward is zero almost surely and $\eta_\pi^{(x,a)} = \delta_0$.

Gerstenberg, Neininger and Spiegel prove the moment transfer for joint kernels (their Theorem 3, part 3, applied in the state-action encoding of their Example 2, for $\gamma \in (0,1)$). Their proof in Section 3.2 bounds the return by the maximum of the $q$-th moment norms of the conditional reward laws given successive indices, a Cauchy-sequence argument in $L^q$; finite $M_q$ makes every such conditional norm finite. Bellemare, Dabney and Munos assume that $Z^\pi$ lies in their space of value distributions with bounded moments and do not derive it.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.2 (the space of value distributions with bounded moments) and Section 3.3.1, paragraph after Lemma 3 ("As we assume all moments are bounded").
- J. Gerstenberg, R. Neininger and D. Spiegel, *On solutions of the distributional Bellman equation*, arXiv:2202.00081v3 (2023), <https://arxiv.org/abs/2202.00081v3>: Theorem 3 (part 3) with its proof in Section 3.2, and Example 2.
