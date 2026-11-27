# Thresholds have list replicability number two despite large Littlestone dimension

For every integer $d \ge 2$, the class of thresholds over $2^d$ points has Littlestone dimension $d$ and list replicability number exactly $2$. More generally, the **proper** list replicability number satisfies $\mathrm{LR}_{\mathrm{p}}(H) \ge \mathrm{HS}(H) - 1$, where $\mathrm{HS}$ is the hollow star number; for $s \ge 3$ the class of $s$ singletons has hollow star number $s$ and proper list replicability number exactly $s - 1$, while its (improper) list replicability number is $2$; for $s \ge 4$ this separates proper from improper list replicability.

## Proof sketch

For thresholds, estimate the threshold location by an empirical quantile and round it to one of two interleaved random grids chosen so that, for every distribution, at most two grid points are likely outputs; the linear order makes the two candidate outputs consistent with the same accuracy guarantee. The hollow star lower bound uses the topological mechanism (a coloring of distributions over a hollow star configuration forced by the Poincaré–Miranda or local Borsuk–Ulam theorem).

## Depends on

- [Global stability and list replicability of learning rules](global-stability-and-list-replicability.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [The list replicability number of the d-dimensional cube is d and dominates the VC dimension](list-replicability-of-cube-and-vc-lower-bound.md)
- [Large Littlestone dimension forces large threshold subclasses](../private-learning-and-littlestone-classes/littlestone-dimension-contains-thresholds.md)

## Sources

- Z. Chase, S. Moran, A. Yehudayoff, "Replicability and Stability in Learning", FOCS (2023), arXiv:2304.03757.
