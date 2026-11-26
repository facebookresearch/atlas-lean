# Lindahl equilibrium yields a fractional core for public goods allocation

In a fractional public goods setting with $n$ agents, a set $P$ of projects with costs, a budget $L$, and concave nondecreasing utilities $u_i(x)$ of the fractional funding vector $x \in [0, 1]^P$ with $\sum_p \mathrm{cost}(p) x_p \le L$, a Lindahl equilibrium (personalized prices $q_{ip} \ge 0$ with $\sum_i q_{ip} = \mathrm{cost}(p)$ for funded projects, each agent maximizing utility subject to spending at most $L/n$) exists, and its allocation lies in the core: no coalition $S$ can use the budget $\lvert S \rvert L/n$ to fund a vector that every member of $S$ strictly prefers. For integral (indivisible) projects with additive utilities, rounding a Lindahl equilibrium gives an additive approximation to the core.

## Proof sketch

Existence follows from a fixed-point argument (or a convex program generalizing the Eisenberg–Gale program for Fisher markets). If a coalition $S$ could fund $y$ preferred by all members, each member's personalized cost of $y$ would exceed $L/n$, since otherwise she would have chosen $y$; summing over $S$ shows $y$ costs more than $\lvert S\rvert L/n$, a contradiction. Rounding uses dependent rounding of the fractional equilibrium.

## Depends on

- [Participatory budgeting with approval ballots and project costs](participatory-budgeting-approval-costs.md)
- [Core of an approval-based committee election](core-of-approval-committee-election.md)

## Proof depends on

- [Core of an approval-based committee election](core-of-approval-committee-election.md)

## Sources

- B. Fain, K. Munagala, N. Shah, "Fair Allocation of Indivisible Public Goods", EC 2018, arXiv:1805.03164.
