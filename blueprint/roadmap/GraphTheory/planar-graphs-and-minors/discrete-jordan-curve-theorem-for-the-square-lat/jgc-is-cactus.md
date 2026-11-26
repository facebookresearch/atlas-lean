# Graphs peelable by leaf edges and disjoint cycles

The graphs on a vertex set $V$ that are peelable by leaf edges and disjoint cycles form the smallest class of simple graphs on $V$ such that:

- the graph with no edges is in the class;
- if $x$ has exactly one neighbour $z$ in $K$ and $K$ with the edge $\{x, z\}$ deleted is in the class, then $K$ is in the class;
- if every vertex of $K$ has degree $0$ or $2$, $c$ is a cycle in $K$, and $K$ with the edges of $c$ deleted is in the class, then $K$ is in the class.

Every derivation is finite and the cycle step applies only to graphs whose vertices all have degree $0$ or $2$, so the class consists of the graphs with finitely many edges built from a disjoint union of finitely many finite cycles (possibly none), all other vertices being isolated, by attaching finitely many pendant edges one at a time; the vertex set $V$ itself need not be finite. Every such graph is a cactus graph (every edge lies on at most one cycle), but not every cactus is in the class: two cycles sharing a vertex have no vertex of degree one, and the shared vertex has degree $4$, so no step applies.
