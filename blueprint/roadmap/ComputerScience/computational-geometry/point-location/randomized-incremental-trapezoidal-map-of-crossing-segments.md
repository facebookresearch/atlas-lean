# Randomized incremental trapezoidal map of crossing segments

Let $S$ be a set of $n$ segments in general position with $K$ pairwise crossings. The randomized incremental construction, which inserts the segments in uniformly random order and locates the left endpoint of each new segment with the history graph of destroyed trapezoids, computes the trapezoidal map of $S$ in expected time $O(n \log n + K)$.

## Depends on

- [Trapezoidal map of possibly crossing segments](trapezoidal-map-of-possibly-crossing-segments.md)
- [Uniformly random rearrangement of a list](../../randomized-algorithms/average-case-running-time/uniform-permutation.md)

## Proof depends on

- [Every trapezoid is determined by at most four segments](every-trapezoid-is-determined-by-at-most-four-segments.md)
- [Number of vertices of the trapezoidal map of crossing segments](number-of-vertices-of-the-trapezoidal-map-of-crossing-segments.md)
- [Expected number of crossings among the first r segments](expected-number-of-crossings-among-the-first-r-segments.md)
- [Expected number of configurations created by randomized incremental construction](../randomized-incremental-construction/expected-number-of-configurations-created-by-randomized-incremental.md)
- [Expected number of conflicts in randomized incremental construction](../randomized-incremental-construction/expected-number-of-conflicts-in-randomized-incremental-construction.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 10 (Trapezoidal maps), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2010.pdf>: Theorem 10.14, from Theorems 10.7 and 10.9, bounding $t_r$ by Observation 10.11 and Lemma 10.12; Lemma 10.8 bounds the history-graph traversals by the number of conflicts
