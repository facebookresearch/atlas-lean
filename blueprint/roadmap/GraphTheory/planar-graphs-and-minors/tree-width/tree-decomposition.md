# Tree-decomposition

Let $G$ be a graph. A tree-decomposition of $G$ is a pair $(T, (V_t)_{t \in T})$ of a finite tree
$T$ and bags $V_t \subseteq V(G)$, one for each node $t$, such that

- (T1) every vertex of $G$ lies in some bag;
- (T2) for every edge of $G$ some bag contains both of its ends;
- (T3) $V_{t_1} \cap V_{t_3} \subseteq V_{t_2}$ whenever $t_2$ lies on the path from $t_1$ to $t_3$ in $T$.

Condition (T3) is equivalent to asking that, for each vertex $v$, the nodes whose bags contain
$v$ span a subtree of $T$. The node type of the tree lives in the same universe as the vertex
type of $G$, and the tree is required to be finite, as for the finite graphs of the source.

## Sources

- Reinhard Diestel, *Graph Theory*, 6th edition, author's online preview of Chapter 12 (PDF dated 28 June 2024), https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch12.pdf, Section 12.3, conditions (T1)–(T3).
