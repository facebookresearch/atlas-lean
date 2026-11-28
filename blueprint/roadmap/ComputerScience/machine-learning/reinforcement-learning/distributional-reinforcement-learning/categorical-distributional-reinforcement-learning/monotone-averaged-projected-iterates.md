# Averaged projected iterates from the grid endpoints converge monotonically

Started from the top and bottom grid endpoints, the averaged projected categorical iterates decrease and increase monotonically in stochastic dominance. Then both converge to the categorical fixed point in the supremum Cramér metric.

Fix a grid $z_1 < z_2 < \dots < z_K$ with $K \ge 2$. Let $\mathsf{p}$ be a reward–transition kernel, $\gamma \in [0,1)$ and $\pi$ a stochastic policy, with $\mathcal{T}^\pi$ the [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md), $\Pi_{\mathcal{C}}$ the [categorical projection](../categorical-distributional-reinforcement-learning/categorical-projection.md), $\eta_{\mathcal{C}}$ the [fixed point of $\Pi_{\mathcal{C}} \mathcal{T}^\pi$](../categorical-distributional-reinforcement-learning/projected-categorical-operator-fixed-point.md), $\bar \ell_2$ the [supremum Cramér metric](../categorical-distributional-reinforcement-learning/cramer-distance.md), and $\preceq$ element-wise [stochastic dominance](../categorical-distributional-reinforcement-learning/categorical-operators-are-monotone.md). Define $U_0^{(x,a)} = \delta_{z_K}$, $L_0^{(x,a)} = \delta_{z_1}$ for every $(x,a)$, and

$$U_{k+1} = \tfrac12 U_k + \tfrac12 \Pi_{\mathcal{C}} \mathcal{T}^\pi U_k, \qquad L_{k+1} = \tfrac12 L_k + \tfrac12 \Pi_{\mathcal{C}} \mathcal{T}^\pi L_k.$$

Then for every $k \ge 0$, $U_{k+1} \preceq U_k$, $L_k \preceq L_{k+1}$ and $L_k \preceq U_k$, and $\bar \ell_2(U_k, \eta_{\mathcal{C}}) \to 0$ and $\bar \ell_2(L_k, \eta_{\mathcal{C}}) \to 0$.

## Depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [The projected categorical operator is a √γ-contraction with a unique fixed point](../categorical-distributional-reinforcement-learning/projected-categorical-operator-fixed-point.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)
- [Distributional Bellman and categorical operators are monotone for stochastic dominance](../categorical-distributional-reinforcement-learning/categorical-operators-are-monotone.md)

## Proof depends on

- [Distributional Bellman and categorical operators are monotone for stochastic dominance](../categorical-distributional-reinforcement-learning/categorical-operators-are-monotone.md)
- [The projected categorical operator is a √γ-contraction with a unique fixed point](../categorical-distributional-reinforcement-learning/projected-categorical-operator-fixed-point.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Expansion

Every grid law is dominated by $\delta_{z_K}$ and dominates $\delta_{z_1}$, so $U_1 \preceq U_0$ and $L_0 \preceq L_1$. The [monotonicity](../categorical-distributional-reinforcement-learning/categorical-operators-are-monotone.md) of $\Pi_{\mathcal{C}} \mathcal{T}^\pi$ and of mixtures gives the inductive steps, and the same argument gives $L_k \preceq U_k$. For one pair, a sequence of grid laws that decreases in dominance has distribution functions that increase pointwise and are bounded by $1$. Their limit is the distribution function of a grid law $\nu^*$, and $\ell_2^2(\nu_k, \nu^*) \le \sum_{i<K} (z_{i+1} - z_i) \max_i |F_k(z_i) - F^*(z_i)|^2 \to 0$ (Rowland's Lemma 7); the same holds for increasing sequences. So $U_k \to U^*$ and $L_k \to L^*$ in $\bar \ell_2$. The map $\eta \mapsto \frac12 \eta + \frac12 \Pi_{\mathcal{C}} \mathcal{T}^\pi \eta$ is $\bar \ell_2$-continuous: mixtures are $\ell_2$-Lipschitz by Minkowski's inequality, and $\Pi_{\mathcal{C}} \mathcal{T}^\pi$ is a contraction. Hence $U^* = \frac12 U^* + \frac12 \Pi_{\mathcal{C}} \mathcal{T}^\pi U^*$, so $U^* = \Pi_{\mathcal{C}} \mathcal{T}^\pi U^*$, and uniqueness of the [fixed point](../categorical-distributional-reinforcement-learning/projected-categorical-operator-fixed-point.md) gives $U^* = \eta_{\mathcal{C}}$; likewise for $L^*$.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: appendix Section 9, Lemma 5 and Lemma 7 with their proofs (the proof of Theorem 1).
