# Every trapezoid is determined by at most four segments

Let $S$ be a set of segments in general position and $R \subseteq S$. For every trapezoid $\square$ of the trapezoidal map of $R$ there is a set $D \subseteq R$ of at most four segments such that $\square$ is a trapezoid of the trapezoidal map of $D$: each non-vertical side lies on a unique segment of $R$ or on the bounding square, and each vertical side lies on the bounding square or is induced by an endpoint, attributed to the topmost segment with that endpoint, or by the crossing of two unique segments, one of which already bounds $\square$. Sides on the bounding square need no generator; for $R = \emptyset$ the square itself is the only trapezoid, with $D = \emptyset$. If $\square$ is taken together with at most one incident vertical edge (its *tail*), at most six segments suffice. Hence trapezoids with tail, with conflicts given by the segments that cross the trapezoid, cut off part of its tail or replace the topmost generator of a vertical side, form a configuration space of dimension at most $6$.

## Depends on

- [Trapezoidal map of possibly crossing segments](trapezoidal-map-of-possibly-crossing-segments.md)
- [Configuration space](../randomized-incremental-construction/configuration-space.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 10 (Trapezoidal maps), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2010.pdf>: Lemma 10.2, Definition 10.3, Lemma 10.4 and Definition 10.5
