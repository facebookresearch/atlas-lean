# Deterministic minimum-cost flow in almost-linear time

There is a deterministic algorithm that, given a directed graph with $m$ edges, integral vertex demands and edge capacities bounded by $U$ in absolute value, and integral edge costs bounded by $C$ in absolute value, computes an exact minimum-cost flow in time

$$
m^{1+o(1)}\log U\log C.
$$

In particular maximum flows in graphs with polynomially bounded integral capacities are computed deterministically in $m^{1+o(1)}$ time.

## Proof sketch

Combine the deterministic reduction *The l1 IPM reduces min-cost flow to an approximate dynamic min-ratio cycle problem* with the deterministic data structure *Deterministic dynamic min-ratio cycle data structure with hidden stability* for $\kappa = m^{-o(1)}$; the $\widetilde{O}(m\kappa^{-2}) = m^{1+o(1)}$ instances cost $m^{1+o(1)}$ in total and yield a flow within additive $1/2$ of optimal. Deterministic flow rounding *Deterministic flow rounding without increasing the cost* turns it into an exact integral optimum without the randomized isolation step, and cost and capacity scaling contribute the $\log U\log C$ factor.

## Depends on

- [Integral minimum-cost flow instances with polynomially bounded data](../almost-linear-flow-interior-point-method/integral-min-cost-flow-instance.md)

## Proof depends on

- [Deterministic dynamic min-ratio cycle data structure with hidden stability](deterministic-dynamic-min-ratio-cycle.md)
- [The l1 IPM reduces min-cost flow to an approximate dynamic min-ratio cycle problem](../almost-linear-flow-interior-point-method/ipm-reduces-to-dynamic-min-ratio-cycle.md)
- [Deterministic flow rounding without increasing the cost](../almost-linear-flow-interior-point-method/deterministic-costed-flow-rounding.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
- Donggu Kang, James Payor, "Flow Rounding", arXiv preprint (2015), arXiv:1507.08139.
