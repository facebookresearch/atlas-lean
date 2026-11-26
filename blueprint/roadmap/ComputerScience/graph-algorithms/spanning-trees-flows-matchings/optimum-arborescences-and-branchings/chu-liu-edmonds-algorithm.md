# The Chu-Liu/Edmonds algorithm

**Chu-Liu/Edmonds** computes a minimum-cost spanning in-arborescence of $(G, c)$ rooted at $r$, where costs lie in a linearly ordered abelian group (negative costs allowed). Each vertex $v \ne r$ selects a cheapest outgoing arc $v \to f(v)$; if no vertex lacks an arc and the selected arcs contain no cycle, they form the answer. If some $v \ne r$ has no outgoing arc, report failure. Otherwise pick a cycle $C$ of selected arcs, contract it to a single vertex $x_C$, and for every arc $u \to v$ with $u \in C$, $v \notin C$ give the contracted arc $x_C \to v$ the cost $c(u, v) - c(u, f(u))$ (reduced cost; equivalently add the cost of the rest of the cycle); recurse on the contracted instance and expand the cycle by keeping all its arcs except the one leaving the vertex whose contracted arc was chosen.

## Depends on

- [Spanning arborescences and branchings](spanning-arborescences-and-branchings.md)

## Sources

- Y.-J. Chu and T.-H. Liu, "On the Shortest Arborescence of a Directed Graph", Scientia Sinica 14, 1965.
- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
- R. E. Tarjan, "Finding Optimum Branchings", Networks 7(1), 1977.
