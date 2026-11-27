# Local Borsuk–Ulam bounds: agnostic list replicability is impossible and finite classes need large lists

(i) **Agnostic impossibility.** A concept class $H$ has $\mathrm{LR}_{\mathrm{agn}}(H) < \infty$, equivalently $\rho_{\mathrm{agn}}(H) > 0$, if and only if $H$ is finite: every proper agnostic learner for a finite class is list replicable with the list $H$, and for every infinite class no agnostic learner is list replicable or globally stable. This contrasts with the realizable setting, where every class of finite Littlestone dimension is list replicable.

(ii) **Realizable bounds.** For every class, $\mathrm{LR}(H) \ge \max\{\mathrm{VC}(H),\, 1 + \lfloor \mathrm{VC}^*(H)/2 \rfloor\}$, where $\mathrm{VC}^*$ is the dual VC dimension, and both terms are sharp. There are classes of Littlestone dimension $d$ with $\mathrm{LR}(H) \ge 2^{d-1}$, an exponential separation from the Littlestone dimension.

(iii) **Local Borsuk–Ulam theorem.** For every open antipodal-free cover of the $d$-sphere $S^d$ some point lies in at least $\lceil (d+3)/2 \rceil$ sets of the cover, and every coloring of the nonempty subsets of $[n]$ in which disjoint sets get different colors has a chain receiving at least $1 + \lfloor n/2 \rfloor$ colors; both bounds are sharp.

## Proof sketch

Map distributions to points of a sphere so that complementary labelings of the same marginal correspond to antipodal points; a list replicable learner induces an open cover of the sphere by the regions where each hypothesis is output with noticeable probability, and in the agnostic case no hypothesis can be good at a point and its antipode. The local Borsuk–Ulam theorem forces a point covered by many sets, which is a distribution at which many hypotheses are each output noticeably often, contradicting a short list. The Kneser chain statement is the combinatorial counterpart used for the dual VC bound.

## Depends on

- [Learners and agnostic PAC learnability](../../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)
- [Global stability and list replicability of learning rules](global-stability-and-list-replicability.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Global stability parameter equals the reciprocal list replicability number](global-stability-equals-reciprocal-list-replicability.md)
- [The list replicability number of the d-dimensional cube is d and dominates the VC dimension](list-replicability-of-cube-and-vc-lower-bound.md)

## Sources

- Z. Chase, B. Chornomaz, S. Moran, A. Yehudayoff, "Local Borsuk-Ulam, Stability, and Replicability", STOC (2024), arXiv:2311.01599.
