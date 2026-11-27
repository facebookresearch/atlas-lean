# Existence and uniqueness of Kelly Nash equilibria and the modified potential

With at least two users and admissible utilities, the price-anticipating game induced by Kelly's mechanism has a unique Nash equilibrium. Its allocation is the unique maximizer of the strictly concave function $\sum_i \hat U_i(d_i)$ over feasible allocations, where $\hat U_i(x) = (1 - x/C)\, U_i(x) + \frac1C \int_0^x U_i(z)\, dz$, and it satisfies the variational inequality $\sum_i U_i'(d_i)(1 - d_i/C)(x_i - d_i) \le 0$ for every feasible $x$.

## Proof sketch

A user's first-order condition with price anticipation is $U_i'(d_i)(1 - d_i/C) = \rho$, which is the KKT condition of maximizing $\sum_i \hat U_i$; $\hat U_i$ is strictly concave, giving existence and uniqueness of the allocation, from which bids are recovered.

## Depends on

- [Kelly's proportional allocation mechanism](kellys-proportional-allocation-mechanism.md)

## Proof depends on

- [Karush–Kuhn–Tucker conditions for inequality constraints](../../../Analysis/convex-analysis-and-variations/karush-kuhn-tucker-inequality.md)
- [Kelly competitive equilibria exist and are socially optimal](kelly-competitive-equilibria-exist-and-are-socially-optimal.md)

## Sources

- Ramesh Johari, "The Price of Anarchy and the Design of Scalable Resource Allocation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ramesh Johari and John N. Tsitsiklis, "Efficiency Loss in a Network Resource Allocation Game", Mathematics of Operations Research, 2004.
