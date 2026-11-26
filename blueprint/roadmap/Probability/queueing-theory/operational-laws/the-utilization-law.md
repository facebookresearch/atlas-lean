# The utilization law

For a resource observed over an interval with $C > 0$ completions, the [operational quantities](operational-quantities-of-an-observation-interval.md) satisfy $U = XS$: the utilization of a resource is the product of its throughput and its average service requirement, since $B/T = (C/T)(B/C)$. For a resource $k$ of a larger system, with system throughput $X$ and service demand $D_k$, likewise $U_k = X_k S_k = X D_k$. For example, a disk serving $40$ requests per second, each requiring $0.0225$ seconds of service, has utilization $0.9$.

## Depends on

- [Operational quantities of an observation interval](operational-quantities-of-an-observation-interval.md)

## Sources

- E. D. Lazowska, J. Zahorjan, G. S. Graham and K. C. Sevcik, *Quantitative System Performance: Computer System Analysis Using Queueing Network Models*, Prentice-Hall, 1984, online edition <https://homes.cs.washington.edu/~lazowska/qsp/>, Chapter 3, Section 3.2 (the utilization law and its example) and Section 3.4 ($U_k = X_k S_k = X D_k$).
