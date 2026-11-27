# Gluing oppositions of blocks

Let $G$ be a graph, let $p$ be a map from its vertices to
an index set, with blocks $B_i = \{v : p(v) = i\}$, and let $f$ be a map from the vertices of $G$
to themselves. Suppose that for every index $i$ there is an opposition of the subgraph of $G$
induced on $B_i$ that agrees with $f$ on $B_i$, and that for all vertices $u, w$ with
$p(u) \neq p(w)$ we have $uw \in E(G) \iff f(u)f(w) \in E(G)$ and
$uf(w) \in E(G) \iff f(u)w \in E(G)$. Then $G$ is opposable.

Since $uf(u)$ and $wf(w)$ are non-edges, the second condition says that the four vertices
$u, f(u), w, f(w)$ induce $C_4$, $2K_2$ or $4K_1$.

## Sources

- Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 2.
