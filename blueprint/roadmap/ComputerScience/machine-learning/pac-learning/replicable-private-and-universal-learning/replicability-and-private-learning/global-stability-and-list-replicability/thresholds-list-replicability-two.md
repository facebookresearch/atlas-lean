# Thresholds have list replicability number two despite large Littlestone dimension

For every integer $d \ge 2$, the class of thresholds over $2^d$ points has Littlestone dimension $d$ and list replicability number exactly $2$. More generally, the **proper** list replicability number satisfies $\mathrm{LR}_{\mathrm{p}}(H) \ge \mathrm{HS}(H) - 1$, where $\mathrm{HS}$ is the hollow star number; for $s \ge 3$ the class of $s$ singletons has hollow star number $s$ and proper list replicability number exactly $s - 1$, while its (improper) list replicability number is $2$; for $s \ge 4$ this separates proper from improper list replicability.

## Proof sketch

For the $t$ thresholds $\tau_1, \dots, \tau_t$, a deterministic proper rule outputs $\tau_{\hat i}$ for the smallest $i$ whose empirical error is below $\sigma_i = \varepsilon/(2(t-i+1))$, a tolerance increasing in $i$. Under a realizable distribution the true errors decrease along $i$ until they reach $0$, so with high probability $\hat i$ is one of the two indices around the first $i$ whose true error is at most $\sigma_i$; both have error at most $\varepsilon$. The lower bound $\mathrm{LR} \ge 2$ follows from the intermediate value theorem. The hollow star lower bound uses the topological mechanism (a coloring of distributions over a hollow star configuration forced by the Poincaré–Miranda or local Borsuk–Ulam theorem).

## Depends on

- [Global stability and list replicability of learning rules](global-stability-and-list-replicability.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [The list replicability number of the d-dimensional cube is d and dominates the VC dimension](list-replicability-of-cube-and-vc-lower-bound.md)
- [Thresholds: VC dimension one but Littlestone dimension $\lfloor \log_2(N+1) \rfloor$, infinite on infinite orders](../../../../online-learning-and-boosting/mistake-bounds-and-littlestone-dimension/thresholds-littlestone-dimension.md)

## Sources

- Z. Chase, S. Moran, A. Yehudayoff, "Replicability and Stability in Learning", FOCS (2023), arXiv:2304.03757, Theorems 5, 6 and 13 and Section 6.3.
