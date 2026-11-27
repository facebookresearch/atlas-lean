# Guaranteed-delay nodes offer burst-delay service curves

For a lossless system and a fixed $T \ge 0$, the system offers to a flow the [service curve](service-curves.md) $\delta_T$, the [burst-delay function](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md), if and only if $R^*(t + T) \ge R(t)$ for all $t \ge 0$. Indeed $(x \otimes \delta_T)(t) = x(t - T)$ for $t \ge T$ and $x(0)$ for $0 \le t < T$, so $R^* \ge R \otimes \delta_T$ says exactly that. The count inequality implies that the [virtual delay](cumulative-flows-backlog-and-virtual-delay.md) is at most $T$ at every time, $d(t) \le T$. The converse holds when $R^*$ is right-continuous, or when $R$ and $R^*$ are both left-continuous, but not in general, since the virtual delay is an infimum: for $T = 1$, $R = \mathbf 1_{[1, \infty)}$ and $R^* = \mathbf 1_{(2, \infty)}$, the virtual delay is $2 - t$ on $[1, 2)$ and $0$ elsewhere, so $d \le 1$, yet $R^*(2) = 0 < R(1)$. When the system is first in, first out for the flow, the virtual delay is the delay of a bit, so under the count inequality every bit leaves within $T$ of its arrival. Without that assumption the count inequality does not identify which bit leaves: if bits arrive at times $1$ and $2$ and the system sends the second at $2$ and the first at $3$, then $R^*(t + 1) \ge R(t)$ for all $t$, yet the first bit waits $2$.

## Depends on

- [Service curves](service-curves.md)
- [Rate-latency, peak-rate, affine and burst-delay functions](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.3.1 (the derivation of equation (1.8)) and Section 1.3.2, Proposition 1.3.3.
