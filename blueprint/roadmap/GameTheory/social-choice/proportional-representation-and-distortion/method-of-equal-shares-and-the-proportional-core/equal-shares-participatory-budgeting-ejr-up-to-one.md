# Equal shares for participatory budgeting satisfies EJR up to one project

In participatory budgeting with additive utilities $u_i(W) = \sum_{p \in W} u_i(p)$, the Method of Equal Shares gives each voter budget $L/n$ and repeatedly funds a project $p$ that is $\rho$-affordable for the least $\rho$, meaning $\sum_i \min(b_i, \rho \cdot u_i(p)) = \mathrm{cost}(p)$ for the current remaining budgets $b_i$, charging each voter $\min(b_i, \rho \cdot u_i(p))$; it stops when no project is affordable. It runs in strongly polynomial time and its outcome satisfies EJR up to one project. For approval utilities ($u_i(p) \in \{0, 1\}$) with arbitrary costs it satisfies EJR exactly. For general additive utilities an EJR outcome always exists, but unless $\mathrm{P} = \mathrm{NP}$ no rule computable in strongly polynomial time satisfies EJR.

## Proof sketch

The budget argument for committees carries over: if an $(\alpha, T)$-cohesive group were under-represented, every payment its members made was at a rate per unit of utility no higher than the rate at which the group could buy $T$, so the group would retain enough money to fund a further project of $T$, contradicting termination unless one more project of $T$ would already satisfy some member. The up-to-one relaxation absorbs the indivisibility of that last project; for approval utilities it never applies, which gives exact EJR. Existence of exact EJR outcomes follows from a greedy rule that repeatedly serves a most cohesive group, and the hardness comes from the single-voter case, in which EJR requires solving a knapsack problem.

## Depends on

- [Participatory budgeting with approval ballots and project costs](participatory-budgeting-approval-costs.md)
- [Method of Equal Shares for approval committees](method-of-equal-shares-approval.md)

## Proof depends on

- [The Method of Equal Shares satisfies extended justified representation and priceability](method-of-equal-shares-ejr-priceability.md)

## Sources

- D. Peters, G. Pierczyński, P. Skowron, "Proportional Participatory Budgeting with Additive Utilities", NeurIPS 2021, arXiv:2008.13276.
