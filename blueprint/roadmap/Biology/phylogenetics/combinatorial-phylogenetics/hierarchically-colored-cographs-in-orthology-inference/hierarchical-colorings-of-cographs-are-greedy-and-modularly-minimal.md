# Hierarchical colorings of cographs are the greedy and modularly-minimal colorings

**Motivation.** In orthology inference, reciprocal best hits between genes define a graph $G$ on genes, and the coloring $\sigma$ assigns each gene its species. If the edges represent orthology correctly, then $(G,\sigma)$ must be a *hierarchically colored cograph* (hc-cograph). This is stronger than the classical requirement that the orthology graph be a cograph, and it constrains which species colorings can occur.

**Definitions.** A *cograph* is $K_1$, a disjoint union of cographs, or a join of cographs; equivalently, it has a cotree $(T,t)$ whose inner nodes are labeled $1$ (join) or $0$ (disjoint union), and each node $u$ induces a subgraph $G(u)$. A vertex coloring $\sigma$ is *hierarchical with respect to a binary cotree* $(T,t)$ if $(G,\sigma)$ is built along $(T,t)$ by the rules
- (K1) a single colored vertex;
- (K2) a join $H_1 \Join H_2$ with $\sigma(V(H_1)) \cap \sigma(V(H_2)) = \emptyset$;
- (K3) a disjoint union $H_1 \,\dot\cup\, H_2$ with $\sigma(V(H_1)) \cap \sigma(V(H_2)) \in \{\sigma(V(H_1)), \sigma(V(H_2))\}$ (one color set contains the other).

For an arbitrary graph, a coloring is *hierarchical* if for every disconnected strong module $G[X]$ some maximal strong submodule $M_j$ has $\sigma(M_i) \subseteq \sigma(M_j)$ for all maximal strong submodules $M_i$ of $G[X]$. It is *modularly minimal* if $|\sigma(G[X])| = \chi(G[X])$ for every strong module $X$ (modules that overlap no other module).

**Theorem.** Let $G$ be a cograph.
1. A coloring hierarchical with respect to a binary cotree $(T,t)$ uses $\chi(G)$ colors, and indeed $|\sigma(G(u))| = \chi(G(u))$ at every cotree node $u$. Conversely, a coloring that is minimal at every node of $(T,t)$ is hierarchical with respect to $(T,t)$.
2. A coloring of $G$ is a **greedy coloring** iff it is hierarchical with respect to **every** binary cotree of $G$. In particular every cograph has a hierarchical coloring with respect to each of its binary cotrees, and one can be computed in polynomial time.
3. For a coloring $\sigma$ of $G$, the following are equivalent: $\sigma$ is hierarchical with respect to some binary cotree; $\sigma$ is minimal along that cotree; $\sigma$ is modularly minimal; $\sigma$ is hierarchical.

Every graph, not only every cograph, admits a hierarchical, a strictly hierarchical, and a modularly-minimal coloring.

## Expansion

The two cotree operations behave differently for coloring. A join forces disjoint color sets, so $\chi$ adds. A disjoint union allows color reuse, and $\chi$ is the maximum over the parts. Rule (K3) says that, at a union, the smaller color set must be reused inside the larger one, which is exactly what keeps the count at $\chi$ at every node. A greedy coloring satisfies this at every union, whatever binary cotree is chosen, because greedy coloring is hereditary on components and each component is colored with an initial segment of the colors. Strong modules of a cograph are exactly the cotree-node subgraphs, which gives the equivalence with modular minimality.

## Sources

- Dulce I. Valdivia, Manuela Geiß, Maribel Hernández Rosales, Peter F. Stadler and Marc Hellmuth, "Hierarchical and Modularly-Minimal Vertex Colorings", arXiv:2004.06340 (2020), Section 2 (Theorems 2.2, 2.6, 2.7, 2.8), Section 3 (Definitions 3.2–3.4, Theorems 3.3, 3.7, 3.8), <https://doi.org/10.48550/arXiv.2004.06340>.
