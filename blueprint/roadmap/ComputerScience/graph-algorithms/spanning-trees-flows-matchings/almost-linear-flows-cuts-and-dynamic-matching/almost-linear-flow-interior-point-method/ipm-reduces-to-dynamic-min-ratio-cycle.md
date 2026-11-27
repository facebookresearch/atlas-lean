# The l1 IPM reduces min-cost flow to an approximate dynamic min-ratio cycle problem

Suppose there is a data structure solving the $\kappa$-approximate dynamic min-ratio cycle problem with hidden stability (see *Approximate dynamic min-ratio cycle problem with hidden stability*) for some $\kappa \in (0, 1]$. Then there is a deterministic algorithm that, given a minimum-cost flow instance with integral costs and capacities bounded by $\exp(\log^{O(1)} n)$ in absolute value, solves $\tau = \widetilde{O}(m\kappa^{-2})$ min-ratio cycle instances that satisfy the hidden stable $\alpha$-flow chasing property for $\alpha = 1/\Theta(\log m)$ and returns a feasible flow whose cost is within additive $1/2$ of optimal. The total size of the update batches is $\sum_t|U^{(t)}| = \widetilde{O}(m\kappa^{-2})$, the data structure operations are invoked $\widetilde{O}(m\kappa^{-2})$ times, and the total number of edges reported by $\mathrm{Detect}$ is $\widetilde{O}(m\kappa^{-2})$. The running time is $\widetilde{O}(m\kappa^{-2})$ plus the time spent in the data structure.

## Proof sketch

Run the potential reduction method of *Potential-reduction l1 IPM: min-cost flow from m^(1+o(1)) approximate min-ratio cycles* from the point of *An initial IPM point with polynomially bounded potential*, with lazily maintained lengths and gradients as in *Lazy maintenance of IPM lengths and gradients with few coordinate changes*; the edges reported by $\mathrm{Detect}$ are exactly those whose $\boldsymbol{\ell}$-weighted movement crossed the threshold and must be refreshed. The witness $\mathbf{c}^{(t)} = \mathbf{f}^* - \mathbf{f}^{(t)}$ has ratio at most $-\alpha/4$ against its width by *The direction to an optimal flow is a good minimum-ratio witness*, and since each iterate moves every coordinate by a small fraction of its residual capacity, the widths change by at most a factor $2$ between refreshes of an edge, which is hidden stability. Refreshing the global cost factor and binary search on $F^*$ add only polylogarithmic overhead.

## Depends on

- [Approximate dynamic min-ratio cycle problem with hidden stability](../dynamic-min-ratio-cycle-data-structures/dynamic-min-ratio-cycle-hidden-stability.md)
- [Hidden stable flow chasing property of a dynamic min-ratio cycle instance](../dynamic-min-ratio-cycle-data-structures/hidden-stable-flow-chasing.md)
- [Integral minimum-cost flow instances with polynomially bounded data](integral-min-cost-flow-instance.md)

## Proof depends on

- [Potential-reduction l1 IPM: min-cost flow from m^(1+o(1)) approximate min-ratio cycles](l1-potential-reduction-ipm.md)
- [Lazy maintenance of IPM lengths and gradients with few coordinate changes](lazy-length-gradient-maintenance.md)
- [An initial IPM point with polynomially bounded potential](ipm-initial-point-construction.md)
- [The direction to an optimal flow is a good minimum-ratio witness](optimal-direction-min-ratio-witness.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
