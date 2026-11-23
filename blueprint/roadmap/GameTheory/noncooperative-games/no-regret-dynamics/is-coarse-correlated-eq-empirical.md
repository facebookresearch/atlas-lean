# No-regret dynamics converge to coarse correlated equilibria

Suppose $T \ge 1$ rounds of a finite game are played and every player's regret against every
fixed strategy is at most $T\varepsilon$. Then the empirical distribution of play is an
$\varepsilon$-coarse correlated equilibrium.

The rounds here are the realised profiles; Roughgarden states the result for the time average of
the product distributions played in each round, of which this is the deterministic case.

## Informally uses

- [Expectations under the empirical distribution](sum-empirical-mul.md): both sides of the
  equilibrium condition become time averages.

## Background

- [Hedge algorithm](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/README.md): background, if every player runs Hedge the hypothesis holds with
  $\varepsilon \to 0$ as $T \to \infty$.

## Sources

- T. Roughgarden, CS364A *Algorithmic Game Theory*, Lecture #17 "No-regret dynamics", Stanford University, 2013, Proposition 3.1.
