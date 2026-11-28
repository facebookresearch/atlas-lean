# The independent rectangle bound lower-bounds OPT

For every permutation access sequence $X$ of length $m$, every arborally satisfied superset of $P(X)$ has at least $\mathrm{IRB}(X)/2 + m$ points, so $\mathrm{OPT}(X) \ge \mathrm{IRB}(X)/2 + m$ in the touched-node cost model. Moreover the independent rectangle bound is equal, up to constant factors, to the output of *Signed Greedy*, which runs Greedy separately on the rectangles of positive slope and on those of negative slope and outputs $\max\{|\mathrm{add}^{+}(X)|, |\mathrm{add}^{-}(X)|\} + m$, where $\mathrm{add}^{\pm}(X)$ are the points added by the two runs. Demaine, Harmon, Iacono, Kane and Pătraşcu also exhibit independent families corresponding to both of Wilber's lower bounds, without a formal proof of the equivalence.

## Proof sketch

Call a superset *signed-satisfied* if it contains one part satisfying all rectangles of positive slope and another satisfying all rectangles of negative slope; every arborally satisfied superset is signed-satisfied. The main theorem shows that every signed-satisfied superset has at least $|I|/2 + m$ points for an independent family $I$, by induction that removes a locally widest rectangle of $I$ and decomposes the rectangles overlapping it. The run of Greedy on one slope class produces exactly as many points as an independent family of that class, and the minimum superset satisfying one class equals that output plus $m$; chaining these facts places Signed Greedy within a factor $4$ of $\mathrm{IRB}(X) + m$.

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
