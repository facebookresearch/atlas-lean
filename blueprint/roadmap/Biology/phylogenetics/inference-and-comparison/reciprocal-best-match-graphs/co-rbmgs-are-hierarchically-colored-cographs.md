# Reciprocal best match graphs that are cographs are hierarchically colored cographs

Let $(G,\sigma)$ be an undirected vertex-coloured graph. For vertex-disjoint coloured graphs $(H,\sigma_H)$ and $(H',\sigma_{H'})$, write $\nabla$ for their join (all edges between them added) and $\dot\cup$ for their disjoint union, with the inherited colouring. A graph $(G,\sigma)$ is a *hierarchically colored cograph* (hc-cograph) if

- (K1) $G = K_1$ is a single coloured vertex; or
- (K2) $(G,\sigma) = (H,\sigma_H) \nabla (H',\sigma_{H'})$ with $\sigma(V(H)) \cap \sigma(V(H')) = \emptyset$; or
- (K3) $(G,\sigma) = (H,\sigma_H) \,\dot\cup\, (H',\sigma_{H'})$ with $\sigma(V(H)) \cap \sigma(V(H')) \in \{\sigma(V(H)), \sigma(V(H'))\}$,

where $(H,\sigma_H)$ and $(H',\sigma_{H'})$ are hc-cographs. A *co-RBMG* is a graph that is both a cograph and a [reciprocal best match graph](connected-components-of-a-reciprocal-best-match-graph.md).

**Theorem.**

1. A vertex-coloured graph $(G,\sigma)$ is a co-RBMG if and only if it is an hc-cograph.
2. Every co-RBMG is explained by its hc-cotree $T^G_{hc}$, the binary tree recording the recursive (K1)–(K3) construction with leaves coloured by $\sigma$.
3. For a properly coloured undirected graph, it can be decided in polynomial time whether it is a co-RBMG, and in the positive case a tree explaining it can be built in polynomial time.

## Depends on

- [Connected components of a reciprocal best match graph](connected-components-of-a-reciprocal-best-match-graph.md)

## Expansion

Dropping the colour constraints in (K2) and (K3) recovers the usual cograph recursion, so hc-cographs are cographs. A join of two graphs on disjoint colour sets is explained by a root with the two explaining subtrees as children: every cross pair is a reciprocal best match because no closer leaf of the same colour exists. A disjoint union whose colour sets are nested is explained similarly, since the subtree carrying all colours absorbs the best matches of the other. Conversely, the cotree of a co-RBMG can be relabelled to satisfy (K2cc) and (K3cc). Recognition reduces to computing the cotree (linear time) and checking the colour constraints at every inner vertex. RBMGs are the graphs on which reciprocal-best-hit orthology inference operates; the cograph case is the one compatible with an orthology relation.

## Sources

- Manuela Geiß, Peter F. Stadler and Marc Hellmuth, *Reciprocal Best Match Graphs*, arXiv:1903.07920, Theorems 9, 10 and 11 (Section "Characterization of $n$-RBMGs"). <https://doi.org/10.48550/arXiv.1903.07920> Published version: Journal of Mathematical Biology 80 (2019) 865–953, <https://doi.org/10.1007/s00285-019-01444-2>.
