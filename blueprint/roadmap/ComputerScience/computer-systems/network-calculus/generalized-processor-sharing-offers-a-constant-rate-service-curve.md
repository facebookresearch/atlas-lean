# Generalized processor sharing offers a constant-rate service curve

A *generalized processor sharing* (GPS) node with total output rate $c$ serves several flows in parallel as a fluid, flow $i$ having a weight $\phi_i > 0$; let $r_i = c\,\phi_i / \sum_j \phi_j$, the sum running over all flows. Its guarantee is that whenever flow $i$ has data in the node throughout an interval $(s, t]$, it receives at least $r_i (t - s)$ of service in it, $R_i^*(t) - R_i^*(s) \ge r_i (t - s)$: the backlogged flows share the rate $c$ in proportion to their weights, so each gets at least its share of the total. Then the node offers to flow $i$ the [service curve](service-curves.md) $\lambda_{r_i}$, the peak-rate function with rate $r_i$.

**Proof.** Fix $t$. If flow $i$ has no backlog at $t$, then $R_i^*(t) = R_i(t) \ge (R_i \otimes \lambda_{r_i})(t)$. Otherwise let $s_0$ be the infimum of the $s$ such that flow $i$ is backlogged throughout $(s, t]$. There are times $w \le s_0$ arbitrarily close to $s_0$ with zero backlog, $R_i(w) = R_i^*(w)$ (at worst $w = 0$, where both vanish), and for every $s \in (s_0, t]$, and for $s = t$ when $s_0 = t$, $R_i^*(t) \ge R_i^*(s) + r_i (t - s) \ge R_i(w) + r_i (t - w) - r_i (s - w)$. Letting $s$ and $w$ tend to $s_0$ gives $R_i^*(t) \ge (R_i \otimes \lambda_{r_i})(t)$; since $\lambda_{r_i}$ is continuous, no continuity of the flows is needed.

## Depends on

- [Service curves](service-curves.md)
- [Rate-latency, peak-rate, affine and burst-delay functions](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.3.1 (the GPS example leading to equation (1.7)) and Section 2.1.2 (the GPS node and its service curve $\lambda_{r_i}$).
