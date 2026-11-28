# Multicalibration as multi-objective learning via game dynamics

Multicalibration with respect to $\mathcal{C}$ can be cast as a multi-objective learning problem, a zero-sum game between a learner choosing predictors and an adversary choosing objectives, triples $(S, v, j)$ of a group, a cell $v$ of a $\lambda$-grid of the prediction space and a class $j$, together with a sign (a distribution over objectives). Running no-regret or best-response dynamics for the two players yields multicalibrated predictors with a unified analysis that recovers known guarantees. When both players run no-regret algorithms, the guarantee is for the uniform mixture of the learner's iterates, a non-deterministic predictor, and such mixtures can be multicalibrated in a very weak sense even when no predictor in their support is calibrated. Deterministic predictors come from the no-regret versus best-response dynamics of Haghtalab, Jordan and Zhao's Algorithm 2: the learner runs Hedge over the $k$ labels at each point, the adversary best-responds at each step through an agnostic learning oracle, and the algorithm returns the single iterate with the lowest empirical multicalibration error on fresh samples. This gives improvements: deterministic multicalibrated predictors whose error on a group $S$ is at most $\varepsilon\sqrt{\Pr[x \in S]}$, from $O(\ln(k)\,(\ln(|\mathcal{S}|/\varepsilon\delta) + k\ln\lambda)/\varepsilon^4)$ samples without knowing the group probabilities, and $O(\ln(k)/\varepsilon^2)$ calls to an agnostic learning oracle for deterministic $k$-class multicalibration, an exponential improvement over the previous $O(k/\varepsilon^2)$.

## Proof sketch

The multicalibration violation is linear in the adversary's mixed strategy, so the value of the game is zero (a perfectly calibrated $p^*$ exists), and no-regret dynamics converge to approximate equilibria at rate given by the regret bounds; for two no-regret players this certifies only the averaged, randomized predictor. For the deterministic conclusion, the learner's Hedge regret over $k$ labels is at most $T\varepsilon/8$ once $T \ge 256\,\varepsilon^{-2}\ln k$, and each adversary step is an $(\varepsilon/8)$-best response from the agnostic learning oracle, so some single iterate $h^{(t)}$ is $(\varepsilon/4)$-optimal; estimating every iterate's multicalibration error on $O(\ln(T/\delta)/\varepsilon^2)$ fresh samples and returning the lowest gives an $(\varepsilon/2)$-optimal, hence multicalibrated, deterministic predictor with probability $1-\delta$, after $T$ oracle calls.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)

## Proof depends on

- [The $\sqrt{T}$ regret bound of Hedge](../online-learning-and-boosting/hedge-algorithm/regret-le-two-sqrt.md)
- [Von Neumann's minimax theorem](../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- N. Haghtalab, M. I. Jordan, E. Zhao, "A Unifying Perspective on Multi-Calibration: Game Dynamics for Multi-Objective Learning", NeurIPS (2023), arXiv:2302.10863, Definition 2.1, Example 4.2, Theorems 4.3 and 5.7, Algorithm 2, Table 1.
