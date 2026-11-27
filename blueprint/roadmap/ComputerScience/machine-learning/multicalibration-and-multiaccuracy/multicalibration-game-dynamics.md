# Multicalibration as multi-objective learning via game dynamics

Multicalibration with respect to $\mathcal{C}$ can be cast as a multi-objective learning problem, a zero-sum game between a learner choosing predictors and an adversary choosing objectives, triples $(S, v, j)$ of a group, a cell $v$ of a $\lambda$-grid of the prediction space and a class $j$, together with a sign (a distribution over objectives). Running no-regret dynamics for the adversary (such as Hedge over $\mathcal{C} \times \text{levels}$) against a best-responding or no-regret learner yields multicalibrated predictors with a unified analysis that recovers known guarantees and gives improvements: deterministic multicalibrated predictors whose error on a group $S$ is at most $\varepsilon\sqrt{\Pr[x \in S]}$, from $O(\ln(k)\,(\ln(|\mathcal{S}|/\varepsilon\delta) + k\ln\lambda)/\varepsilon^4)$ samples without knowing the group probabilities, and $O(\ln(k)/\varepsilon^2)$ calls to an agnostic learning oracle for deterministic $k$-class multicalibration, an exponential improvement over the previous $O(k/\varepsilon^2)$.

## Proof sketch

The multicalibration violation is linear in the adversary's mixed strategy, so the value of the game is zero (a perfectly calibrated $p^*$ exists), and no-regret dynamics converge to approximate equilibria at rate given by the regret bounds. The adversary's Hedge regret is logarithmic in the number of objectives, which yields dependence on $\ln(k|\mathcal{S}|)$; the learner's best response is implemented with an agnostic learning oracle.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)

## Proof depends on

- [The $\sqrt{T}$ regret bound of Hedge](../online-learning-and-boosting/hedge-algorithm/regret-le-two-sqrt.md)
- [Von Neumann's minimax theorem](../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- N. Haghtalab, M. I. Jordan, E. Zhao, "A Unifying Perspective on Multi-Calibration: Game Dynamics for Multi-Objective Learning", NeurIPS (2023), arXiv:2302.10863, Definition 2.1, Theorems 4.3 and 5.7, Table 1.
