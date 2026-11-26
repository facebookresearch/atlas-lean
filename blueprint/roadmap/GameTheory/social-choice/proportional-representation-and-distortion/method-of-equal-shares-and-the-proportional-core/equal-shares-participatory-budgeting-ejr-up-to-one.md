# Equal shares for participatory budgeting satisfies EJR up to one project

In participatory budgeting, the Method of Equal Shares gives each voter budget $L/n$, and repeatedly funds a project $p$ whose supporters can jointly pay $\mathrm{cost}(p)$ while minimizing the maximum per-voter payment $\rho$ relative to the obtained utility, charging each supporter $\min(b_i, \rho \cdot u_i(p))$. For additive utilities it runs in polynomial time and its outcome satisfies EJR up to one project; for approval utilities with arbitrary costs exact EJR outcomes exist but cannot always be found in polynomial time unless $\mathrm{P} = \mathrm{NP}$.

## Proof sketch

The budget argument for committees carries over: a $T$-cohesive group that is underrepresented retains enough money to buy every project of $T$ it does not have, up to the last project, since every payment made per unit of utility is bounded by the price at which the group could have bought $T$. The up-to-one relaxation absorbs the indivisibility of the last project. Existence of exact EJR follows from a greedy cohesive rule, and hardness from a knapsack-type reduction.

## Depends on

- [Participatory budgeting with approval ballots and project costs](participatory-budgeting-approval-costs.md)
- [Method of Equal Shares for approval committees](method-of-equal-shares-approval.md)

## Proof depends on

- [The Method of Equal Shares satisfies extended justified representation and priceability](method-of-equal-shares-ejr-priceability.md)

## Sources

- D. Peters, G. Pierczyński, P. Skowron, "Proportional Participatory Budgeting with Additive Utilities", NeurIPS 2021, arXiv:2008.13276.
