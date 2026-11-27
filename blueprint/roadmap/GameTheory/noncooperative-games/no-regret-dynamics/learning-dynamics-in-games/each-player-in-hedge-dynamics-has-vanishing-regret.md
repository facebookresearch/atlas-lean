# Each player in Hedge dynamics has vanishing regret

In Hedge dynamics on a finite game with costs in $[0, 1]$, run for $T$ rounds with learning rate $\eta_i = \sqrt{\ln |S_i| / T}$, every player $i$ has external regret at most $2\sqrt{T \ln |S_i|}$ against its realized expected-cost vectors. Consequently the time average of the product distributions is an $\varepsilon$-coarse correlated equilibrium with $\varepsilon = \max_i 2\sqrt{\ln |S_i| / T}$.

## Proof sketch

The multiplicative-weights regret bound holds against any loss sequence, adaptive or not, since each player's update depends only on the realized costs. Averaging over rounds converts per-player regret into the coarse correlated equilibrium slack.

## Depends on

- [Hedge (multiplicative-weights) dynamics in a finite game](hedge-multiplicative-weights-dynamics-in-a-finite-game.md)
- [External regret](../../../not-yet-classified/part-02/regret/external-regret.md)
- [Coarse correlated equilibrium](../is-coarse-correlated-eq.md)

## Proof depends on

- [Regret of entropic mirror descent for prediction with expert advice](../../../../Analysis/convex-analysis-and-variations/mirror-descent/multiplicative-weights-regret-le.md)

## Sources

- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
- Sanjeev Arora, Elad Hazan and Satyen Kale, "The Multiplicative Weights Update Method: a Meta-Algorithm and Applications", Theory of Computing, 2012.
