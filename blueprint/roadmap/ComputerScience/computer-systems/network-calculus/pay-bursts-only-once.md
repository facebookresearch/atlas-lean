# Pay bursts only once

Assume a flow with the affine [arrival curve](arrival-curves.md) $\gamma_{r,b}$ traverses two nodes in sequence that offer the rate-latency [service curves](service-curves.md) $\beta_{R_1,T_1}$ and $\beta_{R_2,T_2}$, with $r < R_1$ and $r < R_2$. With $R = \min(R_1, R_2)$, the end-to-end delay is at most

$$
D_0 = \frac{b}{R} + T_1 + T_2,
$$

and $D_0$ is smaller than the sum of the per-node bounds,

$$
D_1 + D_2 = \frac{b}{R_1} + T_1 + \frac{b + rT_1}{R_2} + T_2,
$$

obtained by bounding the delay at the first node, the arrival curve $\gamma_{r, b + rT_1}$ of its output, and the delay at the second node. The term due to the burst $b$ appears once in $D_0$ and twice in $D_1 + D_2$, and the burstiness $rT_1$ added by the first node does not increase the end-to-end bound.

## Depends on

- [Arrival curves](arrival-curves.md)
- [Service curves](service-curves.md)

## Proof depends on

- [Concatenation of rate-latency service curves](concatenation-of-rate-latency-service-curves.md)
- [Bounds for a token-bucket flow at a rate-latency node](bounds-for-a-token-bucket-flow-at-a-rate-latency-node.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.4.3, the paragraph "Pay bursts only once".
