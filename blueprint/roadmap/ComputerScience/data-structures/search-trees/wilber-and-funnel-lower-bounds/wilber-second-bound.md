# Wilber's second lower bound

For every access sequence $X$ on $[n]$, $\mathrm{OPT}(X) = \Omega(\mathrm{W2}(X) - n)$, with an absolute constant.

## Proof sketch

Wilber's original proof is a direct amortized charging argument against an arbitrary BST execution, with an additive $O(n)$ accounting for the initial tree. Geometrically, the funnel of $x_t$ consists of the keys whose last accesses are visible from $(x_t, t)$, and each alternation between keys below and above $x_t$ in this time-ordered list identifies an unsatisfied rectangle of $P(X)$; Demaine, Harmon, Iacono, Kane and Pătraşcu describe an independent family of such rectangles corresponding to the funnel bound, which places it among the independent rectangle lower bounds, though they do not formally prove the equivalence.

## Depends on

- [Wilber's funnel bound](funnel-bound.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Sources

- Robert Wilber, "Lower Bounds for Accessing Binary Search Trees with Rotations", SIAM Journal on Computing 18(1) (1989); FOCS (1986).
- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
