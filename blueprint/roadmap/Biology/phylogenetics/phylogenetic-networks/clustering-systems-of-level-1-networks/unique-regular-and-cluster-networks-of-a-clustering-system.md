# Unique regular and cluster networks of a clustering system

**Setting.** A *network* $N$ on a finite taxon set $X$ is a rooted directed acyclic graph whose leaf set is $X$. For a vertex $v$, its *cluster* $C(v)\subseteq X$ is the set of leaves reachable from $v$, and $\mathscr{C}_N=\{C(v): v\in V(N)\}$ is the set of (hardwired) clusters. A *clustering system* on $X$ is a family $\mathscr{C}\subseteq 2^X$ with $\emptyset\notin\mathscr{C}$, $X\in\mathscr{C}$ and $\{x\}\in\mathscr{C}$ for all $x\in X$; every $\mathscr{C}_N$ is one.

**Definitions.**
- $N$ is *regular* if the map $v\mapsto C(v)$ is an isomorphism from $N$ onto the Hasse diagram $\mathscr{H}[\mathscr{C}_N]$ of $(\mathscr{C}_N,\subseteq)$ (arcs from a cluster to the clusters it covers).
- $N$ satisfies *path-cluster comparability* (PCC) if, for all vertices $u,v$, $u$ and $v$ are comparable in the ancestor order of $N$ exactly when $C(u)\subseteq C(v)$ or $C(v)\subseteq C(u)$.
- $N$ is *semi-regular* if it satisfies (PCC) and has no shortcut (an arc $(u,w)$ together with a longer directed $u$-$w$ path).
- $N$ is *least-resolved* if no network with the same clustering system is obtained from $N$ by deleting shortcuts and contracting arcs.
- $N$ is a *cluster network* if it satisfies (PCC), distinct vertices share a cluster only when one is a hybrid vertex and the other its child, no cluster lies strictly between the clusters of a parent and its child, and every hybrid vertex has exactly one child, which is a tree vertex.

**Statements.**
1. For every clustering system $\mathscr{C}$ there is a unique regular network $N$ with $\mathscr{C}_N=\mathscr{C}$, namely $\mathscr{H}[\mathscr{C}]$.
2. A network is regular if and only if it is semi-regular and has no vertex of out-degree $1$; equivalently, if and only if it is least-resolved and satisfies (PCC).
3. A network is a cluster network if and only if it is semi-regular, *separated* (every hybrid vertex has out-degree $1$ and its child is a tree vertex) and phylogenetic (no vertex of in-degree and out-degree $1$).
4. For every clustering system $\mathscr{C}$ there is a unique cluster network $N$ with $\mathscr{C}_N=\mathscr{C}$. It is obtained from $\mathscr{H}[\mathscr{C}]$ by *expanding* every hybrid vertex $w$: add a new vertex $w'$, redirect all in-arcs of $w$ to $w'$ and add the arc $(w',w)$.
5. A clustering system is *closed* (nonempty intersections of clusters are clusters) if and only if it is the clustering system of an *lca-network*, i.e. one in which every nonempty $A\subseteq X$ has a unique least common ancestor. In that case both the regular and the cluster network of $\mathscr{C}$ are lca-networks.

## Expansion

The Hasse diagram of $\mathscr{C}$ is rooted at $X$ and has the singletons as its leaves, and the cluster of the vertex $C$ is $C$ itself, so it is a regular network for $\mathscr{C}$; any regular network is isomorphic to it by definition, giving uniqueness. A semi-regular network differs from a regular one only by chains of vertices with the same cluster, which are exactly the out-degree-$1$ vertices; forbidding them recovers the Hasse diagram. Expanding a hybrid vertex duplicates its cluster on the new in-degree-$\geq 2$, out-degree-$1$ vertex and leaves (PCC) and shortcut-freeness intact, which produces the separated, phylogenetic, semi-regular network, and the characterization in statement 3 shows there is only one such network per clustering system. For statement 5, in a network satisfying (PCC) the lca of a set $A$ is unique exactly when the clusters containing $A$ have a unique minimal element, which is the closure property.

## Sources

- Marc Hellmuth, David Schaller and Peter F. Stadler, "Clustering systems of phylogenetic networks", Theory in Biosciences 142 (2023), 301–358, <https://doi.org/10.1007/s12064-023-00398-w>; numbering as in arXiv:2204.13466: Definition of cluster networks (Section 4), Proposition 3.42, Theorems 4.8, 4.17, 4.19 and 4.25, Proposition 6.21.
