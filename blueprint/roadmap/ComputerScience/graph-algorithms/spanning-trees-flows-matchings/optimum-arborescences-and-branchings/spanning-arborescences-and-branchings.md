# Spanning arborescences and branchings

Let $G$ be a finite digraph and $r$ a vertex. A **spanning in-arborescence rooted at $r$** is a spanning subdigraph in which every vertex $v \ne r$ has exactly one outgoing arc, $r$ has none, and every vertex reaches $r$; equivalently a **parent function** $p : V \to V$ with $p(r) = r$, $v \to p(v)$ an arc of $G$ for $v \ne r$, and $p^{(i)}(v) = r$ for some $i$. Out-arborescences are defined with arcs reversed. A **branching** is a subdigraph that is a disjoint union of out-arborescences: every vertex has in-degree at most one and there is no directed cycle. For arc costs $c$, the cost of $p$ is $\sum_{v \ne r} c(v, p(v))$.

## Depends on

- [Acyclic directed graph](../../traversal-and-connectivity/topological-sorting/is-acyclic.md)

## Sources

- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
- Y.-J. Chu and T.-H. Liu, "On the Shortest Arborescence of a Directed Graph", Scientia Sinica 14, 1965.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
