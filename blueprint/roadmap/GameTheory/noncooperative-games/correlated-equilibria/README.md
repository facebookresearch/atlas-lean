# Correlated equilibria

A correlated equilibrium (Aumann 1974) is a probability distribution on strategy profiles such that, if a referee draws a profile from it and privately tells each player its own coordinate, no player gains by disobeying its recommendation. In a finite game the correlated equilibria are cut out of the simplex of distributions by finitely many linear inequalities, so they form a compact convex polytope. This polytope contains the Nash equilibria, which are exactly its product distributions (for Nash equilibria described by deviations to pure strategies), and is contained in the Hannan set of coarse correlated equilibria. Even simple games such as Chicken have correlated equilibria outside the convex hull of their Nash equilibria (Hart and Mas-Colell 2000, §2). Correlated equilibria are also what adaptive play reaches: the empirical distribution of play is a correlated approximate equilibrium exactly when every player's conditional regrets are small (Hart and Mas-Colell 2000).

- [Correlated equilibrium](is-correlated-eq.md)
- [Gain from a switched recommendation](switch-gain.md)
- [Correlated-equilibrium sums over a recommendation](sum-mul-switch-gain.md)
- [The set of correlated equilibria is convex](convex-set-of-is-correlated-eq.md)
- [The set of correlated equilibria is closed](is-closed-set-of-is-correlated-eq.md)
- [The set of correlated equilibria is compact](is-compact-set-of-is-correlated-eq.md)
- [Correlated equilibria are coarse correlated equilibria](is-coarse-correlated-eq.md)
- [A pure Nash equilibrium is a correlated equilibrium](is-correlated-eq-dirac.md)

## Nash equilibria as product distributions

- [Product distribution of mixed strategies](product-dist.md)
- [The product distribution is a distribution](is-distribution-product-dist.md)
- [Weight of the opponents' profile](others-weight.md)
- [Expected cost of a pure strategy against mixed opponents](pure-cost.md)
- [Splitting the product weight](product-dist-eq-mul.md)
- [The opponents' weight ignores the own coordinate](others-weight-update.md)
- [Moving a recommendation event](sum-ite-update.md)
- [Expected cost under a product distribution](sum-product-dist-mul.md)
- [Correlated-equilibrium sums of a product distribution](sum-product-dist-mul-switch-gain.md)
- [Nash equilibria are correlated equilibria](is-correlated-eq-product-dist.md)
- [The product correlated equilibria are the Nash equilibria](is-correlated-eq-product-dist-iff.md)
- [Mixed Nash equilibria are correlated equilibria](is-correlated-eq-product-dist-of-is-mixe.md)

## Conditional regrets

- [Conditional regret](cond-regret.md)
- [Conditional regrets are linear in the empirical distribution](cond-regret-div-eq.md)
- [No conditional regret characterises correlated equilibria](is-correlated-eq-empirical-iff.md)
- [Regret-invariant mixed action](is-regret-invariant.md)
- [Blackwell's condition for regret-invariant play](sum-mul-sub-eq-zero-of-is-regret-invaria.md)

## Chicken

- [The game of Chicken](chicken-cost.md)
- [Aumann's correlated distribution for Chicken](chicken-ce.md)
- [Aumann's correlated equilibrium of Chicken](chicken-ce-is-correlated-eq.md)
- [Chicken's correlated equilibrium is not a product](chicken-ce-not-product.md)

## Bayesian rationality

Aumann (1987) derived correlated equilibrium from Bayesian decision theory: in a partition model with a common prior, where each player's action is part of the state of the world, if every player maximises expected payoff given its own information at every state, then the distribution of the action profile is a correlated equilibrium. Conversely, every correlated equilibrium arises in this way.

- [Correlated equilibrium as an expression of Bayesian rationality](is-correlated-eq-of-is-bayes-rational.md)
- [Every correlated equilibrium is the distribution of Bayes-rational play](is-bayes-rational-of-is-correlated-eq.md)
- [Correlated equilibria are exactly the distributions of Bayes-rational play](is-correlated-eq-iff-exists-is-bayes-rat.md)
- [Bayes rationality](is-bayes-rational.md)
- [Conditional expectation given a partition](cond-exp-cell.md)
- [Bayes rationality without normalisation](is-bayes-rational-iff-sum.md)

## Related topics

- [Nash's theorem](../nash-s-theorem/README.md): mixed Nash equilibria, the product correlated equilibria.
- [No-regret dynamics](../no-regret-dynamics/README.md): coarse correlated equilibria (the Hannan set), which contain the correlated equilibria, and the unconditional regrets that lead to them.
- [Adaptive heuristics](../adaptive-heuristics/README.md): regret matching, whose empirical play converges to the set of correlated equilibria.
- [Blackwell approachability](../blackwell-approachability/README.md): the tool that makes conditional regrets vanish.
- [Linear programming](../../../Geometry/convex-geometry/linear-programming/README.md): the correlated equilibria are the feasible set of a linear program, and linear duality proves that it is nonempty (Hart and Schmeidler 1989).
- [Revelation principle](../../mechanism-design/revelation-principle/README.md): the reduction to direct, obeyed recommendations is the revelation argument for mechanisms with private information.
- [Common knowledge and the agreement theorem](../common-knowledge-and-the-agreement-theorem/README.md): the partition model with a common prior that underlies Aumann's Bayesian view of correlated equilibrium.
