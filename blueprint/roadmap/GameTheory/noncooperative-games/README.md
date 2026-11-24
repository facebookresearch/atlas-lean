# Noncooperative games

Noncooperative game theory studies strategic games in which each player chooses a strategy to optimise its own payoff or cost: Nash equilibria and the minimax theorem, potential and congestion games, routing games with Wardrop equilibria, the price of anarchy and of stability, learning dynamics such as no-regret play, regret matching and Blackwell approachability together with correlated and coarse correlated equilibria, and mean field games with a continuum of players.

Every finite game has a mixed equilibrium ([Nash's theorem](nash-s-theorem/README.md), proved from Brouwer's fixed-point theorem); in two-player zero-sum games this is [von Neumann's minimax theorem](von-neumann-s-minimax-theorem/README.md). For two players the [Lemke–Howson algorithm](bimatrix-games-and-the-lemke-howson-algorithm/README.md) finds an equilibrium by following a path, which shows that nondegenerate bimatrix games have an odd number of equilibria; abstracting this argument gives the complexity class [PPAD](../../TheoryOfComputation/completeness-other-classes/ppad-and-the-end-of-the-line-problem/README.md), for which computing approximate Nash equilibria is complete. [Potential games](potential-games/README.md), which include all congestion games by Rosenthal's theorem, even have pure equilibria, reached by best-response dynamics, and in fair cost-sharing network design some equilibrium costs at most $H(k)$ times the optimum. Algorithmic game theory then asks how much selfish behaviour costs, through the price of anarchy that Koutsoupias and Papadimitriou introduced for [selfish load balancing](selfish-load-balancing/README.md), where pure equilibria on $m$ identical machines cost at most $2 - 2/(m+1)$ times the optimum: in [nonatomic routing](selfish-routing-and-the-price-of-anarchy/README.md) Wardrop equilibria exist, have a unique cost and cost at most $4/3$ of the optimum for affine latencies, while [atomic congestion games with affine delays](atomic-congestion-games-with-affine-delays/README.md) have price of anarchy $5/2$. Roughgarden's smoothness arguments make such bounds hold for the outcomes of [no-regret dynamics](no-regret-dynamics/README.md) as well. Learning in repeated games leads to correlated rather than Nash equilibria: [correlated equilibria](correlated-equilibria/README.md) form a polytope containing the Nash equilibria, simple [adaptive heuristics](adaptive-heuristics/README.md) such as regret matching make the empirical distribution of play converge to it, and their analysis rests on [Blackwell approachability](blackwell-approachability/README.md) for games with vector payoffs; uncoupled dynamics, by contrast, cannot guarantee convergence to Nash equilibrium. Aumann showed that correlated equilibrium is also what Bayesian rationality predicts: in a partition model with a common prior, players who maximise expected payoff given their own information play a correlated equilibrium. In the [same model](common-knowledge-and-the-agreement-theorem/README.md), agents whose posteriors for an event are common knowledge cannot agree to disagree. With a continuum of identical players, Lasry and Lions' [mean field games](mean-field-games/README.md) replace the opponents by their distribution; crowd aversion (monotonicity) makes the equilibrium unique, by the argument that gives Wardrop equilibria unique latencies.

- [Nash's theorem](nash-s-theorem/README.md)
- [Von Neumann's minimax theorem](von-neumann-s-minimax-theorem/README.md)
- [Bimatrix games and the Lemke–Howson algorithm](bimatrix-games-and-the-lemke-howson-algorithm/README.md)
- [Potential games](potential-games/README.md)
- [Selfish load balancing](selfish-load-balancing/README.md)
- [Selfish routing and the price of anarchy](selfish-routing-and-the-price-of-anarchy/README.md)
- [Atomic congestion games with affine delays](atomic-congestion-games-with-affine-delays/README.md)
- [No-regret dynamics](no-regret-dynamics/README.md)
- [Correlated equilibria](correlated-equilibria/README.md)
- [Common knowledge and the agreement theorem](common-knowledge-and-the-agreement-theorem/README.md)
- [Blackwell approachability](blackwell-approachability/README.md)
- [Adaptive heuristics](adaptive-heuristics/README.md)
- [Mean field games](mean-field-games/README.md)

## Related topics

- [Cooperative game theory](../cooperative-games/README.md): games with binding agreements, the core and the Shapley value.
- [Linear programming](../../Geometry/convex-geometry/linear-programming/README.md): LP duality, equivalent to the minimax theorem and behind the Bondareva–Shapley theorem.
- [Online learning and boosting](../../ComputerScience/machine-learning/online-learning-and-boosting/README.md): Hedge and weighted majority, the no-regret algorithms used in repeated games.
- [Matchings and flows](../../GraphTheory/matchings-and-flows/README.md): network flows, the combinatorial model behind routing games.
- [Mechanism design](../mechanism-design/README.md): designing the game so that its equilibria, in dominant strategies or Bayesian Nash, achieve a given outcome.
