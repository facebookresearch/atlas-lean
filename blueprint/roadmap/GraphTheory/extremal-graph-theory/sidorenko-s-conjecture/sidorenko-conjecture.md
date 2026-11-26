# Sidorenko's conjecture

For every bipartite simple graph $F$ and every graphon $W$,

$$t(F, W) \ge t(K_2, W)^{|E(F)|} .$$

Equivalently, among graphs with $n$ nodes and edge density $p$, the random graph $G(n, p)$ asymptotically minimizes the number of copies of $F$; or, among bipartite graphs with a given number of edges, a matching has the least density in every graph. This is Lovász's graph form $t(F, G) \ge t(K_2, G)^{|E(F)|}$, for graphons (symmetric, values in $[0, 1]$), which are limits of graphs. Sidorenko's analytic form, inequality (1) in Lovász's paper, is more general: it allows bounded measurable $W \ge 0$ that need not be symmetric, and it implies the form here. It is open; known cases include trees, bigraphs with a colour class of at most four nodes, and cubes (Hatami).

## Background

- [Homomorphism density in a graphon](../../random-graphs/graph-limits/graphon-hom-density.md): the densities in the statement.
- [Sidorenko's inequality for the four-cycle](hom-density-cycle-graph-four-ge.md): the first nontrivial case, for finite weighted graphs.

## Sources

- L. Lovász, "Subgraph densities in signed graphons and the local Sidorenko conjecture", arXiv:1004.3026v1 (2010); published in *Electron. J. Combin.* 18 (2011), §1: the graph form $t(F, G) \ge t(K_2, G)^{|E(F)|}$ (p. 2) and the analytic form, inequality (1).
