# Local surrogate of the expected return

The local surrogate $L_\pi(\tilde\pi)$ predicts the expected discounted return of a new policy $\tilde\pi$ by averaging its advantage over an old policy $\pi$ along the old policy's discounted state visitation, ignoring how the visitation changes with the policy.

Let $(S, A, P, r, \rho_0, \gamma)$ be an infinite-horizon discounted [Markov decision process](../../../../heuristic-search-and-planning/value-iteration/mdp.md) with finite sets of states $S$ and actions $A$, transition probabilities $P(s' \mid s, a)$, reward $r : S \to \mathbb{R}$, initial distribution $\rho_0$ and $\gamma \in (0,1)$. For a [stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md) $\pi$ let

$$\eta(\pi) = \mathbb{E}\Bigl[\sum_{t \ge 0} \gamma^t r(s_t)\Bigr], \qquad s_0 \sim \rho_0,\ a_t \sim \pi(\cdot \mid s_t),\ s_{t+1} \sim P(\cdot \mid s_t, a_t),$$

let $Q_\pi$, $V_\pi$ and the [advantage](../../performance-difference-lemma/advantage.md) $A_\pi = Q_\pi - V_\pi$ be the usual action value, value and advantage, and let $\rho_\pi(s) = \sum_{t \ge 0} \gamma^t \Pr(s_t = s)$ be the unnormalized discounted visitation frequency of $\pi$ from $s_0 \sim \rho_0$. The **local surrogate** of the expected return of $\tilde\pi$ around $\pi$ is

$$L_\pi(\tilde\pi) = \eta(\pi) + \sum_{s \in S} \rho_\pi(s) \sum_{a \in A} \tilde\pi(a \mid s)\, A_\pi(s,a).$$

For comparing policies write $D_{\mathrm{TV}}(p \,\|\, q) = \frac12 \sum_i |p_i - q_i|$, $D^{\max}_{\mathrm{TV}}(\pi, \tilde\pi) = \max_s D_{\mathrm{TV}}(\pi(\cdot \mid s) \,\|\, \tilde\pi(\cdot \mid s))$ and $D^{\max}_{\mathrm{KL}}(\pi, \tilde\pi) = \max_s \mathrm{KL}(\pi(\cdot \mid s) \,\|\, \tilde\pi(\cdot \mid s))$.

## Depends on

- [Markov decision process](../../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)
- [Advantage function](../../performance-difference-lemma/advantage.md)
- [Discounted state occupancy of a policy](../../performance-difference-lemma/occupancy.md)
- [Kullback–Leibler divergence on a finite space](../../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)
- [Total variation distance between finite measures](../../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

None.

## Expansion

In terms of the normalized occupancy $d^\pi_{s_0}$, $\rho_\pi(s) = (1-\gamma)^{-1} \sum_{s_0} \rho_0(s_0)\, d^\pi_{s_0}(s)$. The [performance difference lemma](../../performance-difference-lemma/performance-difference.md) gives the exact identity $\eta(\tilde\pi) = \eta(\pi) + \sum_s \rho_{\tilde\pi}(s) \sum_a \tilde\pi(a \mid s) A_\pi(s,a)$, with the new policy's visitation; the surrogate replaces $\rho_{\tilde\pi}$ by $\rho_\pi$. Since $\sum_a \pi(a \mid s) A_\pi(s,a) = 0$, $L_\pi(\pi) = \eta(\pi)$, and for a differentiable family $\pi_\theta$ the surrogate matches $\eta$ to first order: $\nabla_\theta L_{\pi_{\theta_0}}(\pi_\theta)|_{\theta = \theta_0} = \nabla_\theta \eta(\pi_\theta)|_{\theta = \theta_0}$, an observation of Kakade and Langford. How far the surrogate can be trusted is quantified by the [trust-region policy improvement bound](trust-region-policy-improvement-bound.md). The total variation distance $D_{\mathrm{TV}}$ here is the supremum-over-events distance of probability vectors.

## Sources

- J. Schulman, S. Levine, P. Moritz, M. I. Jordan and P. Abbeel, *Trust Region Policy Optimization*, arXiv:1502.05477v5 (2017), the edition followed for the reward form and the numbering: Section 2, equations (1) to (4), Section 3, equation (7), and the definition of the maximal KL divergence before equation (9). [arXiv](https://arxiv.org/abs/1502.05477v5)
- Original publication: Proceedings of the 32nd International Conference on Machine Learning (ICML 2015), PMLR 37, Sections 2 and 3, which state the same notions for a cost function to be minimized, with the maximal total variation divergence as equation (9). [ICML proceedings](https://proceedings.mlr.press/v37/schulman15.html)
