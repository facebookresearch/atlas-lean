# Expected number of configurations created by randomized incremental construction

Let $S = (X, \Pi, D, K)$ be a configuration space of fixed dimension with $|X| = n$, and let $t_r$ be the expected number of active configurations with respect to a uniformly random $r$-element subset of $X$. Inserting the elements of $X$ in uniformly random order and maintaining $T(R)$, the expected total number of configurations created is

$$O\Big(\sum_{r=1}^{n} \frac{t_r}{r}\Big).$$

## Depends on

- [Configuration space](configuration-space.md)
- [Uniformly random rearrangement of a list](../../randomized-algorithms/average-case-running-time/uniform-permutation.md)

## Proof depends on

- [Expected structural change in randomized incremental construction](expected-structural-change-in-randomized-incremental-construction.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 10 (Trapezoidal maps), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2010.pdf>: Theorem 10.7
- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 8 (The configuration space framework), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%208.pdf>: Section 8.3, from which the bound follows by summing over $r$
