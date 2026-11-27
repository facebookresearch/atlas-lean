# Expected number of conflicts in randomized incremental construction

Let $S = (X, \Pi, D, K)$ be a configuration space of fixed dimension $d$ with $|X| = n$, and let $t_r$ be the expected number of configurations active with respect to a uniformly random $r$-element subset of $X$. A *conflict* is a pair $(\Delta, s)$ with $\Delta \in T_r$ for some step $r$ of the random insertion order and $s \in K(\Delta)$. The expected number of conflicts during the randomized incremental construction of $T(X)$ is

$$O\Big(n \sum_{r=1}^{n} \frac{t_r}{r^2}\Big).$$

In the Delaunay and trapezoidal-map applications, the location cost of the algorithm is bounded by the number of conflicts.

## Depends on

- [Configuration space](configuration-space.md)
- [Uniformly random rearrangement of a list](../../randomized-algorithms/average-case-running-time/uniform-permutation.md)

## Proof depends on

- [Active configurations after adding one element](active-configurations-after-adding-one-element.md)
- [Expected structural change in randomized incremental construction](expected-structural-change-in-randomized-incremental-construction.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 10 (Trapezoidal maps), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2010.pdf>: Theorem 10.9
- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 8 (The configuration space framework), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%208.pdf>: Definition 8.5 (conflict) and Section 8.5 (expected number of conflicts), which uses Lemma 8.6
