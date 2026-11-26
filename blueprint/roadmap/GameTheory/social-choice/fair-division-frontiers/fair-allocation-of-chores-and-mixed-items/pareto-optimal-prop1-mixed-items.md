# Pareto optimal and PROP1 allocations of mixed items in polynomial time

In the mixed fair division model with additive utilities of arbitrary sign, there always exists a complete allocation that is Pareto optimal and PROP1, and such an allocation can be computed in strongly polynomial time.

## Proof sketch

Compute a competitive equilibrium of a fractional market with equal budgets (for mixed manna this is the outcome of a convex program in the spirit of Eisenberg and Gale), whose fractional allocation is Pareto optimal and envy-free. Its consumption graph can be made acyclic without changing utilities; rounding the fractional assignments on the resulting forest so that each agent loses at most one good or gains at most one chore preserves Pareto optimality and yields PROP1.

## Depends on

- [Fair division of mixed goods and chores](mixed-goods-and-chores-model.md)
- [Pareto-optimal allocation](../../../not-yet-classified/part-01/indivisible/is-pareto-optimal.md)

## Proof depends on

- [First welfare theorem: price-supported allocations are fractionally Pareto optimal](../market-equilibria-for-fair-and-efficient-allocation/first-welfare-theorem-mbb-fpo.md)

## Sources

- H. Aziz, H. Moulin, F. Sandomirskiy, "A polynomial-time algorithm for computing a Pareto optimal and almost proportional allocation", Operations Research Letters 48(5) (2020), arXiv:1909.00740.
