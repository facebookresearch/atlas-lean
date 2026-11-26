# Backlog bound for strict service curves

Assume that a lossless node offers a [strict service curve](strict-service-curves.md) $\beta$ to a flow with [arrival curve](../arrival-curves.md) $\alpha$, and that $\alpha(u_0) \le \beta(u_0)$ for some $u_0 > 0$. Then every backlogged period lasts at most $u_0$, and for every $t$

$$
R(t) - R^*(t) \le \sup_{0 \le u < u_0} [R(t) - R(t - u) - \beta(u)] \le \sup_{0 \le u < u_0} [\alpha(u) - \beta(u)] .
$$

So the [backlog bound](../the-backlog-bound.md) need only consider intervals shorter than $u_0$.

## Depends on

- [Strict service curves](strict-service-curves.md)
- [Arrival curves](../arrival-curves.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.4.4, Theorem 1.4.7 with its proof.
