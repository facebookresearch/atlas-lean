# Variable capacity nodes offer strict service curves

Consider a node offering a flow a variable service capacity, described by a cumulative function $M$, where $M(t)$ is the total service available to the flow in $[0, t]$, with a buffer large enough that no data is lost. If $M(t) - M(s) \ge \beta(t - s)$ for all $0 \le s \le t$, for a fixed wide-sense increasing $\beta$ with $\beta(0) = 0$, then $\beta$ is a [strict service curve](strict-service-curves.md) for the flow, and hence, when the input and output cumulative functions are left-continuous, a [service curve](../service-curves.md).

## Depends on

- [Strict service curves](strict-service-curves.md)

## Proof depends on

- [Strict service curves are service curves](strict-service-curves-are-service-curves.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.3.2, Proposition 1.3.6 and the paragraph before it.
