# Generalized processor sharing offers a constant-rate service curve

A *generalized processor sharing* (GPS) node with total output rate $c$ serves several flows in parallel, flow $i$ having a weight $\phi_i > 0$. At every time $t$ it serves flow $i$ at rate $0$ if flow $i$ has no backlog, and otherwise at rate $c\,\phi_i / \sum_{j \in B(t)} \phi_j$, where $B(t)$ is the set of flows backlogged at $t$; so the output of flow $i$ is

$$
R_i^*(t) = \int_0^t \frac{\phi_i}{\sum_{j \in B(s)} \phi_j}\, c\, \mathbf 1\{i \in B(s)\}\, ds .
$$

Then the node offers to flow $i$ the [service curve](service-curves.md) $\lambda_{r_i}$, the peak-rate function with rate $r_i = c\,\phi_i / \sum_j \phi_j$, the sum running over all flows: during each backlogged period of flow $i$ its service rate is at least $r_i$.

## Depends on

- [Service curves](service-curves.md)
- [Rate-latency, peak-rate, affine and burst-delay functions](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.3.1 (the GPS example leading to equation (1.7)) and Section 2.1.2 (the GPS node and its service curve $\lambda_{r_i}$).
