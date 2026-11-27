# Strict service curves are service curves

If a node offers $\beta$ as a [strict service curve](strict-service-curves.md) to a flow, and the input and output [cumulative functions](../cumulative-flows-backlog-and-virtual-delay.md) $R$ and $R^*$ are left-continuous, the source's convention, so that the backlog vanishes at the start of every backlogged period, then it also offers $\beta$ as a [service curve](../service-curves.md) to the flow. Without that assumption the conclusion can fail: for $\beta = \delta_1$, $R = 5 \cdot \mathbf 1_{[1, \infty)}$ and $R^* = 5 \cdot \mathbf 1_{(2, \infty)}$ the only backlogged period is $[1, 2]$, of length $1$, so $\delta_1$ is a strict service curve, yet $(R \otimes \delta_1)(2) = 5 > R^*(2) = 0$. The proof is the busy-period argument: for each $t$, let $t_0$ be the start of the backlogged period containing $t$ (or $t_0 = t$ if there is no backlog); then $R^*(t_0) = R(t_0)$ and $R^*(t) \ge R(t_0) + \beta(t - t_0)$.

## Depends on

- [Strict service curves](strict-service-curves.md)
- [Service curves](../service-curves.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.3.2, Proposition 1.3.5, with the busy-period analysis of the GPS example in Section 1.3.1.
