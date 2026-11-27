# Sequence form and realization plans

For a player $i$ with perfect recall, let $S_i$ be the set of sequences of $i$ that occur on some root-to-leaf path, including the empty sequence $\emptyset$. A *realization plan* is a vector $x \in \mathbb{R}^{S_i}$ with $x \ge 0$, $x(\emptyset) = 1$, and the flow conservation constraints $\sum_{c \in C_h} x(\sigma_h c) = x(\sigma_h)$ for every information set $h \in H_i$. These constraints are written $E x = e$. The realization plan of a mixed or behavior strategy assigns to each sequence the probability that player $i$ makes all choices in it.

## Depends on

- [Perfect recall](perfect-recall.md)

## Sources

- Bernhard von Stengel, "Efficient Computation of Behavior Strategies", Games and Economic Behavior, 1996.
- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
