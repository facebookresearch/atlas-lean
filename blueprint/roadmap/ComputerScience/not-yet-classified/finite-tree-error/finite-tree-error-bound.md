# Finite tree error bound

Backward-induction error bound on a finite binomial tree.

Let `E` follow the exact Snell update for exercise payoff `g` with up
probability `p ∈ [0, 1]` and discount factor `disc > 0`, and let `V` start
from the same terminal values while each backward update deviates from the
exact update by at most `ε ≥ 0`. Then after `N` steps the values differ by at
most `ε * ∑ j ∈ Finset.range N, disc ^ j` at every node.
