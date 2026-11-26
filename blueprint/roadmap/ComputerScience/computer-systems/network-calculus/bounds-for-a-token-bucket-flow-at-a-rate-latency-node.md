# Bounds for a token-bucket flow at a rate-latency node

Assume a flow with the affine [arrival curve](arrival-curves.md) $\gamma_{r,b}$ is served by a node that offers the rate-latency [service curve](service-curves.md) $\beta_{R,T}$, with $r \le R$ and $R > 0$. Then the backlog is at most $b + rT$, the virtual delay is at most $T + b/R$, and the output flow has the arrival curve $\gamma_{r, b + rT}$: the node increases the burstiness of the flow by $rT$. If $r > R$, the backlog and delay bounds are infinite. With $T = 0$, a flow constrained by one leaky bucket and served at a constant rate $R \ge r$ needs a buffer of $b$: $r$ is the minimum rate required to serve the flow, and $b$ the buffer required to serve it at any constant rate at least $r$.

## Depends on

- [Arrival curves](arrival-curves.md)
- [Service curves](service-curves.md)

## Proof depends on

- [The backlog bound](the-backlog-bound.md)
- [The delay bound](the-delay-bound.md)
- [The output arrival curve](the-output-arrival-curve.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.4.1, Figure 1.10 and the paragraph "A simple example and interpretation of leaky bucket" that follows it.
