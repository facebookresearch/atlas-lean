# Backlog bound for super-additive service curves

Assume that a lossless node offers a [service curve](../service-curves.md) $\beta$ to a flow with a finite sub-additive [arrival curve](../arrival-curves.md) $\alpha$ ($\alpha(t) < \infty$ for every $t$, so that the differences below are defined), that $\beta$ is super-additive ($\beta(s + t) \ge \beta(s) + \beta(t)$), and that $\alpha(u_0) \le \beta(u_0)$ for some $u_0 > 0$. Then for every $t$

$$
R(t) - R^*(t) \le \sup_{0 \le u < u_0} [R(t) - R(t - u) - \beta(u)] \le \sup_{0 \le u < u_0} [\alpha(u) - \beta(u)] .
$$

Super-additivity holds for rate-latency service curves; unlike the [strict case](backlog-bound-for-strict-service-curves.md), nothing is claimed about the length of backlogged periods.

## Depends on

- [Service curves](../service-curves.md)
- [Arrival curves](../arrival-curves.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.4.4, Theorem 1.4.8 with its proof.
