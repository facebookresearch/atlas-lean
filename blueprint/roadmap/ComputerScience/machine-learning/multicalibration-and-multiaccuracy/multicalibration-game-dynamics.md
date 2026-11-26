# Multicalibration as multi-objective learning via game dynamics

Multicalibration with respect to $\mathcal{C}$ can be cast as a multi-objective learning problem, a zero-sum game between a learner choosing predictors and an adversary choosing pairs $(c, v)$ of a group function and a level (a distribution over objectives). Running no-regret dynamics for the adversary (such as Hedge over $\mathcal{C} \times \text{levels}$) against a best-responding or no-regret learner yields multicalibrated predictors with a unified analysis that recovers known guarantees and gives improvements: multicalibration conditions whose error on a group of measure $\mu(S)$ scales with $\sqrt{\mu(S)}$, and an exponential improvement in the number of classes $k$ for $k$-class multicalibration.

## Proof sketch

The multicalibration violation is linear in the adversary's mixed strategy, so the value of the game is zero (a perfectly calibrated $p^*$ exists), and no-regret dynamics converge to approximate equilibria at rate given by the regret bounds. The adversary's Hedge regret is logarithmic in the number of objectives, which yields sample complexity logarithmic in $|\mathcal{C}|$; group-size-adaptive bounds come from adaptive learning rates.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)

## Proof depends on

- [The $\sqrt{T}$ regret bound of Hedge](../online-learning-and-boosting/hedge-algorithm/regret-le-two-sqrt.md)
- [Von Neumann's minimax theorem](../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- N. Haghtalab, M. I. Jordan, E. Zhao, "A Unifying Perspective on Multi-Calibration: Game Dynamics for Multi-Objective Learning", NeurIPS (2023), arXiv:2302.10863.
