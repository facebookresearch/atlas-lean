# Labellable networks among tree-based, orchard and tree-sibling networks

**Setting.** Rooted phylogenetic networks as in the labelling construction: $N$ is labellable iff no two distinct non-leaf vertices have the same set of children. A network is *tree-based* if it has a spanning tree whose leaves are the leaves of $N$. It is *orchard* if it is non-degenerate and reduces to a single vertex by cherry and reticulated-cherry reductions. It is *tree-sibling* if every set of siblings contains a tree vertex (a vertex of in-degree $1$), and *tree-child* if every vertex is *visible*, meaning some leaf has every root-to-leaf path through it.

**Results.**

1. *Tree-based networks.* A non-degenerate tree-based network is labellable iff $c_N(x) \ne c_N(y)$ for all distinct **tree** vertices $x, y$. A binary tree-based network is labellable iff $p_N(x) \ne p_N(y)$ for every pair of reticulations $x, y$, where $p_N$ denotes the parent set.
2. *Not nested.* Some tree-based networks are not labellable (two tree vertices with the same two reticulate children), and some labellable networks are not tree-based (one containing a zig-zag path between two reticulations).
3. *Orchard networks are labellable.* Equivalently, no orchard network has two vertices with the same set of children.
4. *Visibility.* In any network, if $c_N(u) = c_N(v)$ for $u \ne v$, then neither $u$ nor $v$ is visible. Hence tree-child networks, and the normal networks contained in them, are labellable.
5. *Tree-sibling networks are labellable.*
6. *Derived network.* The relation $x \sim y \iff c_N(x) = c_N(y)$ is an equivalence. Quotienting by it, and repeating until no two vertices share a child set, gives a labellable network $D(N)$ on the same leaf set. The map $N \mapsto D(N)$ is canonical and idempotent, and it fixes normal networks: $D(\mathcal{N}(N)) = \mathcal{N}(N)$ for the normalization $\mathcal{N}$. In general $\mathcal{N}(D(N)) \ne \mathcal{N}(N)$.

## Depends on

- [Labellable phylogenetic networks and expanding covers](labellable-networks-and-expanding-covers.md)

## Expansion

(1) In a non-degenerate tree-based network, two reticulations with equal child sets would share a single reticulate child. Tree-based networks forbid that configuration. A reticulation (one child) and a tree vertex (at least two children) never have equal child sets, so only tree vertices can collide. In the binary case, equal child sets of two tree vertices are two reticulations with the same two parents. (3) Orchard networks are tree-based, so a failure of labellability would come from two tree vertices $u_1, u_2$ sharing $k \ge 2$ children. That substructure contains a copy of $K_{2,k}$, and no binary resolution of a network containing $K_{2,k}$ admits an HGT-consistent labelling, the known characterization of non-binary orchard networks. (4) If $u$ were visible through leaf $i$, a root-to-$i$ path through a child $x$ of $u$ could be rerouted through $v$, which avoids $u$ by acyclicity, a contradiction. (5) A tree vertex has a single parent, so two sibling sets that both contain a tree vertex cannot have the same parents. (6) Each quotient step strictly reduces the vertex count, so the iteration terminates in a network with injective child map. Normal networks are tree-child, hence already labellable.

## Sources

- A. Francis, M. Steel, "Labellable phylogenetic networks", Bulletin of Mathematical Biology 85 (2023) 46, Corollary 6.1, Theorem 6.3, Fig. 5, Theorem 6.4, Corollary 6.5, Lemma 6.6, Corollary 6.7 and the section on derived networks, <https://doi.org/10.1007/s11538-023-01157-0> (PMC10129972).
