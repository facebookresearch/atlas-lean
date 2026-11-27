# Lindahl equilibrium yields a fractional core for public goods allocation

In a fractional public goods setting with $n$ agents, a set $P$ of projects with costs, a budget $L$, and continuous, concave, nondecreasing utilities $u_i(x)$ of the funding vector $x \in [0, 1]^P$ with $\sum_p \mathrm{cost}(p) x_p \le L$, a Lindahl equilibrium exists: personalized prices $q_{ip} \ge 0$ with $\sum_i q_{ip} \le \mathrm{cost}(p)$ for every project, with equality when $x_p > 0$, such that $x$ maximizes each agent's utility among funding vectors she can pay for with $L/n$ at her prices. Its allocation lies in the core with endowments: no coalition $S$ can use the budget $\lvert S \rvert L/n$ to fund a vector that every member of $S$ strictly prefers. For indivisible projects with additive utilities the core can be empty, but additive approximations of it can be computed in polynomial time, for example an outcome in the core up to an additive $2$ (in units of the largest single-project utility) under matroid constraints, and under packing constraints such as a budget an additive error logarithmic in the width of the constraints.

## Proof sketch

Existence follows from a fixed-point argument. For the core property, if a coalition $S$ could fund $y$ preferred by all members, then each member's personalized cost of $y$ would exceed $L/n$, since otherwise she would have chosen $y$; summing over $S$ and using $\sum_i q_{ip} \le \mathrm{cost}(p)$ shows that $y$ costs more than $\lvert S\rvert L/n$, a contradiction. The indivisible guarantees maximize smoothed Nash welfare objectives, adding a constant to each agent's utility, and round fractional solutions of the corresponding convex programs.

## Depends on

- [Participatory budgeting with approval ballots and project costs](participatory-budgeting-approval-costs.md)
- [Core of an approval-based committee election](core-of-approval-committee-election.md)

## Sources

- D. K. Foley, "Lindahl's Solution and the Core of an Economy with Public Goods", Econometrica 38(1) (1970).
- B. Fain, K. Munagala, N. Shah, "Fair Allocation of Indivisible Public Goods", EC 2018, arXiv:1805.03164.
