# Disjoint-set data structure

Union-find represents each class by a rooted tree of parent pointers. In the parent-forest
model, a depth certificate that strictly decreases along parent pointers bounds the cost of
find, and union links the root of one class to the root of the other. In the array-based
structure, union links roots by rank and find compresses the path it follows. Linking by rank
gives every root at least $2^{\mathrm{rank}}$ nodes, hence paths of at most
$\lfloor \log_2 n \rfloor$ edges and an $O(n + m \log n)$ cost bound; with compression,
Tarjan and van Leeuwen prove the bound $O(n + m\,\alpha(m + n, n))$ (J. ACM 31(2) (1984)).

- [Parent forest with a depth certificate](forest.md)
- [Root of a vertex in a parent forest](find.md)
- [Path length to the root](path-length.md)
- [Find with cost](find-with-cost.md)
- [Equivalent vertices of a parent forest](equivalent.md)
- [Find returns a root](find-is-root.md)
- [Find is unchanged along a parent pointer](find-parent.md)
- [Every vertex is equivalent to its representative](find-in-class.md)
- [The cost of find is the path length plus one](find-with-cost-time.md)
- [The cost of find is at most the depth certificate plus one](find-with-cost-time-le-depth.md)
- [Parent map after linking two roots](link-parent.md)
- [Depth certificate after linking two roots](link-depth.md)
- [Linking two roots of a parent forest](link.md)
- [Union in a union-find forest](union.md)
- [Representatives after a union](find-union.md)
- [Union makes its arguments equivalent](union-equivalent.md)
- [Union of equivalent vertices changes nothing](union-eq-self-of-equivalent.md)
- [Equivalence after a union](equivalent-union-iff.md)
- [Union preserves the representatives of unrelated classes](find-union-of-unrelated.md)
- [Union in a parent forest with cost](union-with-cost.md)
- [Cost bound for union in a parent forest](union-with-cost-time-le-depth.md)
- [Correctness of the union-find equivalence query](check-equiv-spec.md)
- [Connected components via union-find](connected-components.md)
- [Connected components allocates $n$ nodes](connected-components-size.md)
- [Connected components computes reachability](connected-components-equiv-iff-reachable.md)
- [Operation counts of connected components](connected-components-time-spec.md)
- [Cost-counted FIND auxiliary](counted-aux.md)
- [The cost-counted FIND auxiliary returns the uncounted result](counted-aux-ret.md)
- [Cost of the FIND auxiliary at a root](counted-aux-time-root.md)
- [Cost recurrence of the FIND auxiliary at a non-root](counted-aux-time-step.md)
- [Root tests exceed parent writes by one](counted-aux-time-balance.md)
- [Cost-counted FIND](counted-find.md)
- [The cost-counted FIND returns the FIND result](counted-find-ret.md)
- [Parent writes are bounded by the rank gap](counted-aux-writes-rank.md)
- [FIND compresses exactly the original path to the root](find-parent-eq-ite-iterate.md)
- [Effect of path-compressing find on each node](get-elem-find.md)
- [The root is reached in fewer parent steps than there are nodes](exists-first-iterate-root-d.md)
- [Ranks after linking two nodes of an array](rank-d-link-aux.md)
- [Ranks after linking in a union-find structure](rank-link.md)
- [Linking two roots by rank](root-d-link-eq-ite.md)
- [Union is two finds followed by a link](union-carried.md)
- [Path compression preserves ranks](rank-find.md)
- [Ranks after a union](rank-union.md)
- [Linking by rank with operation counts](counted-link-aux.md)
- [Counted linking returns the linked array](counted-link-aux-ret.md)
- [Operation counts of linking by rank](counted-link-aux-time.md)
- [Union by rank with operation counts](counted-union.md)
- [Counted union returns the union's array](counted-union-ret.md)
- [The FIND phases of a union make two more root tests than parent writes](counted-union-find-balance.md)
- [Union-find structures built by make-set, find and union](reachable.md)
- [Class size in a union-find structure](class-size.md)
- [Rank invariant of linking by rank](rank-bounded.md)
- [Rank lemma for linking by rank (roots)](two-pow-rank-le-class-size.md)
- [Ranks are at most $\lfloor \log_2 n \rfloor$](rank-le-log.md)
- [Find paths have at most $\lfloor \log_2 n \rfloor$ edges](iterate-parent-log.md)
- [Rank bounds for union-find built by the public operations](reachable-state-rank-bounds-for-canonical-union/README.md)
- [Set-union operations](op.md)
- [Length of a find path](find-path-length.md)
- [Find paths are short under union by rank](find-path-length-le-log.md)
- [One set-union operation with its cost](step.md)
- [A sequence of set-union operations with its total cost](run.md)
- [Number of make-set operations](num-make-set.md)
- [Number of finds](num-finds.md)
- [Cost bound $O(n + m \log n)$ for union by rank with path compression](run-cost-le-log.md)
- [Cost bound $O(n + m \log n)$ from the empty structure](run-empty-cost-le-log.md)
- [Tarjan–van Leeuwen's Ackermann function](ackermann-tv-l.md)
- [Inverse Ackermann function of Tarjan and van Leeuwen](inverse-ackermann-tv-l.md)
- [Tarjan–van Leeuwen bound for union by rank with path compression](run-empty-cost-le-inverse-ackermann.md)

## Related topics

- [Amortized analysis](../../amortized-analysis/README.md): the potential method, of which
  the inverse-Ackermann bound is an amortized instance.
- [Link-cut tree](../link-cut-tree/README.md): the other dynamic-forest structure of this field.
- [Spanning trees, flows and matchings](../../../graph-algorithms/spanning-trees-flows-matchings/README.md):
  Kruskal's algorithm, which uses union-find.
