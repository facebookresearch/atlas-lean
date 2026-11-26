# Exchange lemma for cycle contraction

Suppose every vertex $v \ne r$ selects a cheapest arc $v \to f(v)$ and $C$ is a cycle of selected arcs. Then every spanning in-arborescence $t$ of the original instance rooted at $r$ contracts to a spanning in-arborescence of the contracted instance whose reduced cost is at most the cost of $t$ minus $\sum_{u \in C} c(u, f(u))$; and conversely every arborescence of the contracted instance expands to one of the original instance whose cost is its reduced cost plus $\sum_{u \in C} c(u, f(u))$.

## Proof sketch

Keep the arc out of $C$ of the vertex of $C$ closest to $r$ in $t$, let the other vertices of $C$ follow the cycle, and redirect arcs into $C$ to $x_C$; replacing a non-selected arc of a cycle vertex by its selected arc never increases cost.

## Depends on

- [The Chu-Liu/Edmonds algorithm](chu-liu-edmonds-algorithm.md)

## Sources

- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
