# Wilber's second lower bound

For every access sequence $X$, $\mathrm{OPT}(X) = \Omega(\mathrm{W2}(X) - n)$, with an absolute constant.

## Proof sketch

The funnel keys of $x_t$ are exactly the keys whose last-access points are visible from $(x_t, t)$ in the geometric view, and each alternation between the two sides of the funnel identifies an unsatisfied rectangle; these rectangles over all $t$ form an independent family, so the bound follows from the independent rectangle bound (Wilber's original proof is a direct charging argument on rotations).

## Depends on

- [Wilber's funnel bound](funnel-bound.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Proof depends on

- [The independent rectangle bound lower-bounds OPT](../geometric-view-of-bst-access/independent-rectangle-lower-bound.md)

## Sources

- Robert Wilber, "Lower Bounds for Accessing Binary Search Trees with Rotations", SIAM Journal on Computing 18(1) (1989); FOCS (1986).
- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
