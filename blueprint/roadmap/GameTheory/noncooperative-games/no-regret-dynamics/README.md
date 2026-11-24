# No-regret dynamics

When a game is played repeatedly and every player uses a no-regret learning algorithm, the empirical distribution of play converges to the set of coarse correlated equilibria. Roughgarden's smoothness framework shows that price-of-anarchy bounds proved by a smoothness argument hold for these outcomes too, so the time-averaged social cost of no-regret play is nearly as good as that of any Nash equilibrium. A simple strategy with vanishing regret is unconditional regret matching, which plays each action with probability proportional to the positive part of its average regret; it is Blackwell's approachability strategy for the nonpositive orthant of regret vectors (Hart and Mas-Colell 2000, Theorem B).

- [Distribution on strategy profiles](is-distribution.md)
- [Coarse correlated equilibrium](is-coarse-correlated-eq.md)
- [Empirical distribution of play](empirical.md)
- [Expectations under the empirical distribution](sum-empirical-mul.md)
- [The empirical distribution is a distribution](is-distribution-empirical.md)
- [Regret against a fixed strategy](regret.md)
- [No-regret dynamics converge to coarse correlated equilibria](is-coarse-correlated-eq-empirical.md)
- [Social cost](social-cost.md)
- [Smooth game](is-smooth.md)
- [Extension theorem for coarse correlated equilibria](expected-social-cost-le.md)
- [Robust price of anarchy for no-regret dynamics](average-social-cost-le.md)

## Unconditional regret matching

- [Regret vector](regret-vector.md)
- [Unconditional regret matching](urm.md)
- [Regret-matching probabilities are nonnegative](urm-nonneg.md)
- [Regret-matching probabilities add up to one](sum-urm.md)
- [Coordinates of the expected regret vector](mixed-payoff-regret-vector-apply.md)
- [Nonpositive orthant](orthant.md)
- [Positive part of a vector](pos-part.md)
- [Negative part of a vector](neg-part.md)
- [A vector minus its negative part](sub-neg-part.md)
- [Positive and negative parts are orthogonal](inner-pos-part-neg-part.md)
- [Distance to the nonpositive orthant](norm-pos-part-eq-inf-dist.md)
- [Norm of the negative part](norm-neg-part-le.md)
- [Regret matching meets Blackwell's condition with equality](inner-pos-part-mixed-payoff-urm.md)
- [Unconditional regret matching has vanishing expected regret](average-regret-le-of-urm.md)

## Related topics

- [Hedge algorithm](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/README.md): a no-regret algorithm with its loss bounds.
- [Potential games](../potential-games/README.md): pure Nash equilibria and best-response dynamics, the equilibria that no-regret outcomes generalise.
- [Von Neumann's minimax theorem](../von-neumann-s-minimax-theorem/README.md): in two-player zero-sum games, no-regret play approaches the value of the game.
- [Atomic congestion games with affine delays](../atomic-congestion-games-with-affine-delays/README.md): a smooth class of games, with robust price of anarchy $5/2$.
- [Correlated equilibria](../correlated-equilibria/README.md): the conditional version, reached when conditional regrets vanish; correlated equilibria are coarse correlated equilibria.
- [Blackwell approachability](../blackwell-approachability/README.md): the vector-payoff theorem behind regret-based strategies.
