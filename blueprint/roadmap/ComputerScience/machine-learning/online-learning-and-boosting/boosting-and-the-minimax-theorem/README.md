# Boosting and the minimax theorem

Freund and Schapire's game-theoretic account of boosting: weak learnability on every distribution over the instances, combined with von Neumann's minimax theorem for the mistake matrix, yields a single weighting of the hypotheses under which the target is a weighted majority vote. AdaBoost approximates such a weighting by running multiplicative weights on the dual game.

- [The mistake matrix](mistake-matrix.md)
- [Weak learnability gives a mixed hypothesis that errs on every instance with probability at most $1/2 - \gamma$](exists-forall-mistake-le.md)
- [The weighted majority vote](weighted-vote.md)
- [Under $\gamma$-weak learnability with $\gamma > 0$, the target is a weighted majority vote](exists-weighted-vote-eq.md)

## Related topics

- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/README.md): the theorem applied to the mistake matrix.
- [Hedge algorithm](../hedge-algorithm/README.md): the multiplicative-weights method whose regret bound proves the minimax theorem and, run on the dual game, gives boosting.
- [AdaBoost](../adaboost/README.md): the algorithm that approximates the weighting.
- [Weak learnability](../../pac-learning/weak-learnability/README.md): the PAC notion of which this is the finite, distribution-by-distribution form.
