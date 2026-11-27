# Trust-region policy improvement bound

The expected return of any new policy is at least the local surrogate minus a penalty quadratic in the largest per-state total variation distance from the old policy. With a KL penalty, maximizing the penalized surrogate with exact advantages yields policies whose returns never decrease.

In the setting of the [local surrogate](local-surrogate-of-the-expected-return.md) (finite states and actions, state reward $r$, $\gamma \in (0,1)$), let $\pi_{\mathrm{old}}$ and $\pi_{\mathrm{new}}$ be stochastic policies, $\alpha = D^{\max}_{\mathrm{TV}}(\pi_{\mathrm{old}}, \pi_{\mathrm{new}})$ and $\varepsilon = \max_{s,a} |A_{\pi_{\mathrm{old}}}(s,a)|$. Then

$$\eta(\pi_{\mathrm{new}}) \ge L_{\pi_{\mathrm{old}}}(\pi_{\mathrm{new}}) - \frac{4\varepsilon\gamma}{(1-\gamma)^2}\, \alpha^2.$$

Consequently, for all stochastic policies $\pi, \tilde\pi$, with $\varepsilon = \max_{s,a} |A_\pi(s,a)|$,

$$\eta(\tilde\pi) \ge L_\pi(\tilde\pi) - C\, D^{\max}_{\mathrm{KL}}(\pi, \tilde\pi), \qquad C = \frac{4\varepsilon\gamma}{(1-\gamma)^2}.$$

For a sequence of policies $\pi_0, \pi_1, \dots$ put $M_i(\pi) = L_{\pi_i}(\pi) - C_i D^{\max}_{\mathrm{KL}}(\pi_i, \pi)$ with $C_i$ the constant $C$ for $\pi = \pi_i$. Then $\eta(\pi_{i+1}) - \eta(\pi_i) \ge M_i(\pi_{i+1}) - M_i(\pi_i)$, so if each $\pi_{i+1}$ maximizes $M_i$ (the exact-advantage policy iteration scheme of the source), then $\eta(\pi_0) \le \eta(\pi_1) \le \eta(\pi_2) \le \cdots$.

## Depends on

- [Local surrogate of the expected return](local-surrogate-of-the-expected-return.md)

## Proof depends on

- [Performance difference lemma](../../performance-difference-lemma/performance-difference.md)
- [Maximal couplings realize statistical distance](../../../../../Probability/foundations/statistical-distance-and-couplings/maximal-coupling-theorem.md)
- [Pinsker's inequality, square-root form](../../../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/total-variation-dist-le-sqrt-kl-div.md)

## Expansion

Write $\bar A(s) = \sum_a \pi_{\mathrm{new}}(a \mid s) A_{\pi_{\mathrm{old}}}(s,a)$. By the performance difference lemma, $\eta(\pi_{\mathrm{new}}) - L_{\pi_{\mathrm{old}}}(\pi_{\mathrm{new}}) = \sum_t \gamma^t (\mathbb{E}_{s_t \sim \pi_{\mathrm{new}}} \bar A(s_t) - \mathbb{E}_{s_t \sim \pi_{\mathrm{old}}} \bar A(s_t))$. At each state couple the two action distributions so that they disagree with probability at most $\alpha$; since $\mathbb{E}_{a \sim \pi_{\mathrm{old}}} A_{\pi_{\mathrm{old}}}(s,a) = 0$, this gives $|\bar A(s)| \le 2\alpha\varepsilon$. Coupling whole trajectories, the two state distributions at time $t$ agree unless a disagreement occurred before $t$, which has probability at most $1 - (1-\alpha)^t$; hence the $t$-th term is at most $4\alpha\varepsilon(1 - (1-\alpha)^t)$ in absolute value. Summing, $|\eta(\pi_{\mathrm{new}}) - L_{\pi_{\mathrm{old}}}(\pi_{\mathrm{new}})| \le 4\alpha^2\gamma\varepsilon/((1-\gamma)(1-\gamma(1-\alpha))) \le 4\alpha^2\gamma\varepsilon/(1-\gamma)^2$. The KL form follows from $D_{\mathrm{TV}}(p \,\|\, q)^2 \le \mathrm{KL}(p \,\|\, q)$, a weakening of Pinsker's inequality, applied state by state. For the monotonicity, $\eta(\pi_{i+1}) \ge M_i(\pi_{i+1})$ by the KL form and $\eta(\pi_i) = M_i(\pi_i)$; this is a minorization-maximization scheme.

The bound extends the conservative policy iteration bound of Kakade and Langford ([conservative policy iteration improves the policy](../../performance-difference-lemma/cpi-improvement.md)) from mixture policies to arbitrary pairs of stochastic policies. The guarantee is for exact advantages and the penalty $C$. The practical trust region policy optimization algorithm replaces the penalty by a constraint on the average KL divergence and uses sample estimates, which the source calls a heuristic approximation; the guarantee does not transfer to it, nor to clipped surrogates such as [PPO's](ppo-clipped-surrogate-objective.md).

The statement follows arXiv:1502.05477v5. The original ICML 2015 publication states Theorem 1 for costs, with the constant $2\varepsilon\gamma/(1-\gamma)^2$ and an $\varepsilon$ defined through the auxiliary policy of conservative policy iteration.

## Sources

- J. Schulman, S. Levine, P. Moritz, M. I. Jordan and P. Abbeel, *Trust Region Policy Optimization*, arXiv:1502.05477v5 (2017), the edition followed for the statement and constants: Theorem 1, equations (8) to (10), Algorithm 1 and Appendix A (Lemmas 1 to 3 and equations (41) to (45)). [arXiv](https://arxiv.org/abs/1502.05477v5)
- Original publication: Proceedings of the 32nd International Conference on Machine Learning (ICML 2015), PMLR 37, Section 3 (cost form, constant $2$ in the statement of Theorem 1). [ICML proceedings](https://proceedings.mlr.press/v37/schulman15.html)
