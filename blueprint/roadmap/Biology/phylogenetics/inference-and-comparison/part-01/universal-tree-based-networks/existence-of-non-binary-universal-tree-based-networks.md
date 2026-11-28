# Existence of non-binary universal tree-based networks

**Setting.** Let $X=\{1,\dots,n\}$. A *rooted phylogenetic network* on $X$ is a rooted acyclic digraph without parallel edges whose root has out-degree at least $2$, whose out-degree-$0$ vertices (leaves) have in-degree $1$ and are identified with $X$, and whose other vertices are either *tree vertices* (in-degree $1$, out-degree $\ge2$) or *reticulations* (in-degree $\ge2$, out-degree $1$). An *unrooted* network is a connected simple graph without degree-$2$ vertices whose degree-$1$ vertices are identified with $X$. A network is *non-binary* if these degrees are not required to be exactly $2$ (rooted) or $3$ (unrooted).

A network $N$ is *tree-based* if it has a spanning tree $T$ whose leaf set is exactly $X$ (a *support tree*); suppressing degree-$2$ vertices of $T$ gives a *base tree*. $N$ is *universal* if every phylogenetic tree on $X$ (binary or not) is a base tree of $N$.

**Theorem.** For every $n\ge1$:

1. there is a rooted non-binary universal tree-based network with $n$ leaves;
2. there is an unrooted non-binary universal tree-based network with $n$ leaves.

## Expansion

The rooted construction has two layers. The upper layer $U_n$ starts from a rooted star with root $\rho$ and leaves $1,\dots,n$, subdivides the root–leaf edges into alternating reticulation and tree vertices $r_l^k,t_l^k$ ($k=1,\dots,n-2$), and adds "horizontal" edges $t_i^k\to r_{i+1}^k$, "diagonal" edges $t_i^k\to r_j^{k+1}$ in both directions, and edges from the outer paths (leaves $1$ and $n$) into every reticulation at the same level. Induction on $n$ shows that every non-binary *tree shape* on $n$ leaves embeds as a base tree: pick a cherry parent $w\ne\rho$ with $k$ children, delete its children, embed the smaller shape in $U_{n-k+1}$, relabel it inside $U_n$, and re-route paths through the new attachment points so that every vertex is covered. A lower layer that realizes any permutation of the leaves (a complete bipartite graph $K_{n,n}$ or a Beneš network) then turns "every shape" into "every leaf-labelled tree". The unrooted statement follows from the rooted one by the known passage from rooted to unrooted universal networks. This extends the binary results, where rooted universal tree-based networks need $\Omega(n\log n)$ reticulations and $O(n\log n)$ suffice.

## Sources

- Mareike Fischer, Michelle Galla, Kristina Wicke, "Non-binary universal tree-based networks", arXiv:2001.06093 (2020), Section 2, Theorem 1 and Corollary 1, <https://doi.org/10.48550/arXiv.2001.06093>.
