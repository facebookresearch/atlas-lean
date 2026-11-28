# Means under a distributional optimality operator contract

For a product kernel, whatever greedy selection rule it uses, a distributional Bellman optimality operator moves means exactly as the expected Bellman optimality map does. Then means contract in the sup norm and converge geometrically to the optimal action values.

Let $\mathsf{p}$ be a [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) with $M_1 < \infty$ and $\gamma \in [0,1)$, and define $\Phi : \mathbb{R}^{\mathcal{X} \times \mathcal{A}} \to \mathbb{R}^{\mathcal{X} \times \mathcal{A}}$ by

$$\Phi(q)(x,a) = \bar r(x,a) + \gamma \sum_{x' \in \mathcal{X}} P(x' \mid x,a) \max_{a' \in \mathcal{A}} q(x',a').$$

Then $\Phi$ has a unique fixed point $q^*$. Assume moreover that $\mathsf{p}$ is a product kernel $R(x,a) \otimes P(\cdot \mid x,a)$ with $M_q < \infty$ for every $q \ge 1$. Then for every [distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md) $\mathcal{T}$, whatever its greedy selection rule, and all $\eta, \mu$ in $\mathscr{P}_\infty(\mathbb{R})^{\mathcal{X} \times \mathcal{A}} = \bigcap_{q \ge 1} \mathscr{P}_q(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ (Bellemare, Dabney and Munos's value distributions with bounded moments) with mean vectors $m(\cdot)$ (notation of [return-distribution functions](../return-distributions-and-policy-evaluation/return-distribution-function.md)),

$$m(\mathcal{T}\eta) = \Phi(m(\eta)), \qquad \|m(\mathcal{T}\eta) - m(\mathcal{T}\mu)\|_\infty \le \gamma \, \|m(\eta) - m(\mu)\|_\infty,$$

and the iterates $\eta_k = \mathcal{T}^k \eta_0$ of any $\eta_0 \in \mathscr{P}_\infty(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ satisfy $\|m(\eta_k) - q^*\|_\infty \le \gamma^k \|m(\eta_0) - q^*\|_\infty$.

## Depends on

- [Distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md)
- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)

## Proof depends on

- [Distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md)
- [Mean of the distributional Bellman update](../return-distributions-and-policy-evaluation/mean-of-the-distributional-bellman-update.md)
- [Greedy policies for a return-distribution function](../distributional-control/greedy-policies-for-return-distributions.md)

## Expansion

By the [mean identity](../return-distributions-and-policy-evaluation/mean-of-the-distributional-bellman-update.md), $m(\mathcal{T}\eta) = m(\mathcal{T}^{\pi_\eta}\eta) = \bar r + \gamma P^{\pi_\eta} m(\eta)$, and greediness of $\pi_\eta$ at every next state $x'$ replaces $\sum_{a'} \pi_\eta(a' \mid x') m(\eta)(x',a')$ by $\max_{a'} m(\eta)(x',a')$, which gives $\Phi(m(\eta))$. Since $|\max_{a'} u(a') - \max_{a'} v(a')| \le \max_{a'} |u(a') - v(a')|$ and the transition probabilities sum to one, $\Phi$ is $\gamma$-Lipschitz for the sup norm. $\mathbb{R}^{\mathcal{X} \times \mathcal{A}}$ is complete, so the contraction mapping theorem (Mathlib's `ContractingWith.fixedPoint`) gives the unique fixed point $q^*$, and $\|m(\eta_k) - q^*\|_\infty = \|\Phi^k(m(\eta_0)) - \Phi^k(q^*)\|_\infty \le \gamma^k \|m(\eta_0) - q^*\|_\infty$. With rewards replaced by their means, $q^*$ is the optimal action-value function. The selection rule enters only through greediness, so the bound holds for every rule, including rules that look at more than the means. Bellemare, Dabney and Munos's proof writes $\|Z_1 - Z_2\|$ in its last line where the mean vectors are meant.

**Scope.** The existence of $q^*$ uses only $M_1 < \infty$ and holds for joint kernels; Rowland and coauthors use it in that setting (the optimal action values in their Theorem 2). The operator statements are Bellemare, Dabney and Munos's, for product kernels in their bounded-moment space, where $\mathcal{T}$ maps that space into itself because the distributional Bellman operator preserves $q$-th moments under $M_q < \infty$. The same linearity computation gives them for joint kernels with $\eta, \mu \in \mathscr{P}_1$; that extension is derived here and is not part of the statement.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.4, Lemma 4, proved in Appendix B.
- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.3, Theorem 2 and its proof in Appendix C (the optimal action values for the joint kernel).
