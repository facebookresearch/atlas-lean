# Hedge algorithm

- [Hedge weight update](update.md)
- [Hedge weights after a sequence of rounds](weights.md)
- [Total weight of the Hedge experts](total.md)
- [Loss of a Hedge round](round-loss.md)
- [Loss of the Hedge algorithm](alg-loss.md)
- [Total loss of an expert](expert-loss.md)
- [The exponential lies below its chord on the unit interval](exp-neg-mul-le.md)
- [A round costs weight in proportion to the algorithm's loss](total-update-le.md)
- [Losses in the unit interval](bounded.md)
- [Weight decay over a Hedge run](total-weights-le.md)
- [Closed form of the Hedge weights](weights-apply.md)
- [The Hedge loss bound](alg-loss-le.md)

## The second-order bound

- [Weighted second moment of a Hedge round](round-sq.md)
- [Summed second moments of the Hedge losses](alg-sq.md)
- [Nonnegative losses](nonneg.md)
- [A round costs weight in proportion to the algorithm's loss, up to a second-order term](total-update-le-sq.md)
- [Weight decay over a Hedge run, second-order form](total-weights-le-sq.md)
- [The second-order Hedge bound](alg-loss-le-sq.md)

## Splitting a run

- [A Hedge run splits at any round](weights-append.md)
- [The Hedge loss splits at any round](alg-loss-append.md)
- [The summed second moments split at any round](alg-sq-append.md)

## The $\sqrt{T}$ regret bound

- [Second moment of a round with losses in the unit interval](round-sq-le-one.md)
- [Summed second moments over $T$ rounds](alg-sq-le-length.md)
- [Regret of Hedge for losses in the unit interval](regret-le.md)
- [The $\sqrt{T}$ regret bound of Hedge](regret-le-two-sqrt.md)

## Related topics

- [No-regret dynamics](../../../../GameTheory/noncooperative-games/no-regret-dynamics/README.md): when every player of a game runs a no-regret algorithm such as Hedge, play approaches the coarse correlated equilibria, and smoothness bounds the average social cost.
- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/README.md): Freund and Schapire's proof of the minimax theorem by multiplicative weights.
- [Natural policy gradient](../../reinforcement-learning/natural-policy-gradient/README.md)
- [Mirror descent](../../../../Analysis/convex-analysis-and-variations/mirror-descent/README.md): the normalized Hedge update is the prox step of mirror descent with the entropy on the simplex. Hedge's regret bounds here are proved by the potential argument, not derived from the mirror descent bounds; the [mirror descent regret bound for experts](../../../../Analysis/convex-analysis-and-variations/mirror-descent/multiplicative-weights-regret-le.md), $\log n/\gamma + \gamma N/2$ for losses in $[-1, 1]$, is a different inequality of the same order for the same update.
- [Boosting and the minimax theorem](../boosting-and-the-minimax-theorem/README.md): Freund and Schapire obtain boosting by running this algorithm on the dual of the mistake game.
- [AdaBoost](../adaboost/README.md): Hedge over the training points with an adaptive step size.
