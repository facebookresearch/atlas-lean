# Proportional fairness maximizes the sum of logarithms

In the [network model](network-model-and-feasible-rate-allocations.md), assume every source uses at least one link. Then there is exactly one [proportionally fair](proportionally-fair-rate-allocations.md) allocation, and it is the unique maximizer of

$$
J(x) = \sum_{s=1}^{S} \ln x_s
$$

over the feasible allocations (with $\ln 0 = -\infty$).

**Proof.** $J$ is strictly concave and continuous with values in $[-\infty, \infty)$ on the compact convex feasible set, which contains a positive allocation; so it has exactly one maximizer, which is positive. At a positive $x$ the aggregate proportional change towards $y$ is $\nabla J(x) \cdot (y - x)$; it is $\le 0$ for all feasible $y$ exactly when $x$ maximizes the concave $J$ on the convex feasible set.

## Depends on

- [Proportionally fair rate allocations](proportionally-fair-rate-allocations.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.2, Theorem 1.2.6 with its proof.
- F. P. Kelly, "Charging and rate control for elastic traffic", *European Transactions on Telecommunications* 8(1):33–37, 1997.
