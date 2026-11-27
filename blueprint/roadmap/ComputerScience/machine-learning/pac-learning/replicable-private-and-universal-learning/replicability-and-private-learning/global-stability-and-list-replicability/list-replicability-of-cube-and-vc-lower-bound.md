# The list replicability number of the d-dimensional cube is d and dominates the VC dimension

For every $d \in \mathbb{N}$ the class $\{\pm1\}^d$ of all functions on a $d$-point domain has list replicability number exactly $d$. Consequently $\mathrm{LR}(H) \ge \mathrm{VC}(H)$ for every class $H$, and for every $\rho_0 > 0$ there is a finite class with $0 < \rho(H) < \rho_0$. Since every finite class has, for every $\rho > 0$, a $\rho$-replicable learner (agreement probability at least $1-\rho$) that uses shared randomness, it follows that replicable learners for such classes cannot be derandomized: for deterministic learners replicability and global stability coincide.

## Proof sketch

The lower bound is topological: identify distributions on the $d$ points labelled by $\pm 1$ with points of a simplex and color each distribution by the hypothesis the learner most likely outputs. List size $L < d$ would give a coloring of the boundary of the cube $[-1,1]^d$ in which opposite faces receive disjoint colors; the Poincaré–Miranda theorem then produces a distribution at which at least $d$ hypotheses are each output with non-negligible probability. The upper bound $\mathrm{LR} \le d$ is an explicit algorithm. The bound $\mathrm{LR}(H) \ge \mathrm{VC}(H)$ follows by restricting to a shattered set of size $d$, where $H$ contains the whole cube, and $0 < \rho(H) = 1/d$ for the cube with $d > 1/\rho_0$.

## Depends on

- [Global stability and list replicability of learning rules](global-stability-and-list-replicability.md)

## Proof depends on

- [Global stability parameter equals the reciprocal list replicability number](global-stability-equals-reciprocal-list-replicability.md)

## Sources

- Z. Chase, S. Moran, A. Yehudayoff, "Replicability and Stability in Learning", FOCS (2023), arXiv:2304.03757, Theorems 1 and 3, Lemma 4, the discussion after Theorem 1, and Sections 4 and 6.1.
