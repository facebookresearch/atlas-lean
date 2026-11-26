# The independent rectangle bound lower-bounds OPT

For every access sequence $X$, $\mathrm{OPT}(X) = \Omega(m + \mathrm{IRB}(X))$. Moreover the independent rectangle bound is equal up to a constant factor to the cost of *Signed Greedy* (Greedy run separately on the rectangles of positive slope and on those of negative slope), and it dominates both of Wilber's lower bounds up to constant factors.

## Proof sketch

Every arborally satisfied superset must place, for every unsatisfied rectangle of the independent family, at least one point that serves no other rectangle of the family, which is a charging argument made possible by independence; with the geometric characterization of OPT this gives the bound. Signed Greedy satisfies only one slope class and produces an independent family of comparable size, and Wilber's bounds are exhibited as particular independent families.

## Depends on

- [Independent rectangle bound](independent-rectangle-bound.md)
- [Geometric Greedy (Greedy Future)](geometric-greedy.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)
- [Wilber's interleave (alternation) bound](../wilber-and-funnel-lower-bounds/interleave-bound.md)
- [Wilber's funnel bound](../wilber-and-funnel-lower-bounds/funnel-bound.md)

## Proof depends on

- [Geometric characterization of the optimal offline BST cost](geometric-characterization-of-opt.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
