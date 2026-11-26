# Guaranteed-delay nodes offer burst-delay service curves

For a lossless bit-processing system, the delay of every bit of a flow is bounded by a fixed $T \ge 0$ if and only if the system offers to the flow the [service curve](service-curves.md) $\delta_T$, the [burst-delay function](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md). Indeed $(x \otimes \delta_T)(t) = x(t - T)$ for $t \ge T$ and $x(0)$ otherwise, so $R^* \ge R \otimes \delta_T$ says $R^*(t + T) \ge R(t)$ for all $t$, which is the delay bound.

## Depends on

- [Service curves](service-curves.md)
- [Rate-latency, peak-rate, affine and burst-delay functions](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.3.1 (the derivation of equation (1.8)) and Section 1.3.2, Proposition 1.3.3.
