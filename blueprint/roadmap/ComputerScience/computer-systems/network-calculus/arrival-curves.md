# Arrival curves

Let $\alpha$ be a wide-sense increasing function defined for $t \ge 0$. A flow with [cumulative function](cumulative-flows-backlog-and-virtual-delay.md) $R$ is *constrained by* $\alpha$, or has $\alpha$ as an *arrival curve*, or is $\alpha$-smooth, if

$$
R(t) - R(s) \le \alpha(t - s) \qquad \text{for all } s \le t .
$$

The condition bounds the data in every window, the windows overlapping. With the peak-rate function $\alpha = \lambda_r$ the flow is peak-rate limited; with the [affine function](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md) $\alpha = \gamma_{r,b}$, the *token bucket* or leaky-bucket constraint, the flow may send a burst of $b$ at once but no more than rate $r$ in the long run, $b$ being the burst tolerance and $r$ the rate.

## Depends on

- [Cumulative flows, backlog and virtual delay](cumulative-flows-backlog-and-virtual-delay.md)
- [Rate-latency, peak-rate, affine and burst-delay functions](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.2.1, Definition 1.2.1 and the discussion of affine arrival curves $\gamma_{r,b}$ that follows it.
