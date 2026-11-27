# Pareto optimal and PROP1 allocations of mixed items in polynomial time

In the mixed fair division model with additive utilities of arbitrary sign, there always exists a complete allocation that is fractionally Pareto optimal (hence Pareto optimal) and PROP1, and such an allocation can be computed in strongly polynomial time. The result also holds for weighted PROP1 with asymmetric entitlements.

## Proof sketch

Start from the equal division, which is proportional, and compute a fractionally Pareto optimal fractional allocation that Pareto-dominates it and whose consumption graph (agents joined to the items they share) is acyclic; such an allocation maximizes a weighted utilitarian welfare and remains proportional. The consumption graph is then a forest. Round it by exploring each tree breadth-first from an agent and giving every shared item entirely to one of the agents sharing it, in favour of the agent currently being explored; acyclicity ensures that each agent loses at most one shared good or gains at most one shared chore relative to her proportional share, which gives PROP1. Since every item stays with an agent who consumed it before, the weighted-welfare certificate of fractional Pareto optimality still applies.

## Depends on

- [Fair division of mixed goods and chores](mixed-goods-and-chores-model.md)
- [Pareto-optimal allocation](../../../not-yet-classified/part-01/indivisible/is-pareto-optimal.md)

## Sources

- H. Aziz, H. Moulin, F. Sandomirskiy, "A polynomial-time algorithm for computing a Pareto optimal and almost proportional allocation", Operations Research Letters 48(5) (2020), arXiv:1909.00740.
