# Means under a distributional optimality operator contract

Whatever greedy selection rule it uses, a distributional Bellman optimality operator moves means exactly as the expected Bellman optimality map does. Then means contract in the sup norm and converge geometrically to the optimal action values.

Let $\mathsf{p}$ be a [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) with $M_1 < \infty$ and $\gamma \in [0,1)$, and define $\Phi : \mathbb{R}^{\mathcal{X} \times \mathcal{A}} \to \mathbb{R}^{\mathcal{X} \times \mathcal{A}}$ by

$$\Phi(q)(x,a) = \bar r(x,a) + \gamma \sum_{x' \in \mathcal{X}} P(x' \mid x,a) \max_{a' \in \mathcal{A}} q(x',a').$$

Then $\Phi$ has a unique fixed point $q^*$. For every [distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md) $\mathcal{T}$, whatever its greedy selection rule, and all $\eta, \mu \in \mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ with mean vectors $m(\cdot)$ (notation of [return-distribution functions](../return-distributions-and-policy-evaluation/return-distribution-function.md)),

$$m(\mathcal{T}\eta) = \Phi(m(\eta)), \qquad \|m(\mathcal{T}\eta) - m(\mathcal{T}\mu)\|_\infty \le \gamma \, \|m(\eta) - m(\mu)\|_\infty,$$

and the iterates $\eta_k = \mathcal{T}^k \eta_0$ of any $\eta_0 \in \mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ satisfy $\|m(\eta_k) - q^*\|_\infty \le \gamma^k \|m(\eta_0) - q^*\|_\infty$.

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

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.4, Lemma 4, proved in Appendix B.
