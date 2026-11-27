# Hedge (multiplicative-weights) dynamics in a finite game

In a finite cost-minimization game with costs in $[-M, M]$, *Hedge dynamics* with learning rates $\eta_i > 0$ start every player with weight $1$ on each pure strategy. In round $t$, player $i$ plays the mixed strategy $p^t_i$ proportional to its current weights, observes its expected-cost vector $C_i(p^t; a)$ against the current product profile, and multiplies the weight of each strategy $a$ by $\exp(-\eta_i C_i(p^t; a))$. The players' cost sequences are coupled through the joint profile, so each player faces an adaptive but deterministic loss sequence.

## Depends on

- [Hedge weights after a sequence of rounds](../../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/weights.md)
- [Mixed Nash equilibrium](../../nash-s-theorem/is-mixed-nash.md)

## Sources

- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
- Sanjeev Arora, Elad Hazan and Satyen Kale, "The Multiplicative Weights Update Method: a Meta-Algorithm and Applications", Theory of Computing, 2012.
