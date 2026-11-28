# NP-completeness of recognising unrooted tree-based networks

Let $N$ be an unrooted phylogenetic network on $X$ (degrees $1$ or $3$, leaves exactly $X$). A phylogenetic tree $T$ on $X$ is a **base-tree** of $N$ if $T$ is obtained from some support tree of $N$ (a spanning tree of $N$ with leaf set $X$) by suppressing its degree-$2$ vertices. Consider the decision problems

- **Unrooted tree-based:** given $N$, is $N$ tree-based?
- **Unrooted base-tree containment:** given $N$ and a phylogenetic tree $T$ on $X$, is $T$ a base-tree of $N$?

**Theorem.** Both problems are NP-complete, already for networks on two leaves.

This contrasts with rooted phylogenetic networks, where deciding tree-basedness is polynomial (base-tree containment is NP-complete in both settings).

**Rooted–unrooted correspondence.** For a leaf $x \in X$, $N$ is tree-based if and only if some orientation of its edges turns $N$ with $x$ and its pendant edge removed into a rooted tree-based network on $X \setminus \{x\}$. Consequently, for every non-empty $X$ there is a *universal* unrooted tree-based network on $X$, having every phylogenetic tree on $X$ as a base-tree.

## Proof depends on

- [HAMILTONIAN CIRCUIT ON PLANAR CUBIC GRAPHS is NP-complete](../../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/hamiltonian-circuit-on-restricted-graph-classes/hamiltonian-circuit-cubic-planar-np-comp.md)

## Expansion

Both problems are in NP because a candidate spanning tree can be checked in polynomial time. For hardness, take a cubic graph $C$, choose an edge $e$, and subdivide it twice, attaching new leaves $x$ and $y$; call the result $C_e(x,y)$. A support tree of a network with two leaves is a Hamiltonian path between them, so the following are equivalent: $C$ is Hamiltonian; $C_e(x,y)$ is tree-based for some $e$; $C_e(x,y)$ has a support tree that is an $x$–$y$ path, i.e. the one-edge tree on $\{x,y\}$ is a base-tree. Since Hamiltonicity of planar cubic $3$-connected graphs is NP-complete, and only $3|V(C)|/2$ edges need to be tried, both problems are NP-hard. For the correspondence, orient a support tree away from $x$ and direct each remaining edge away from its earlier endpoint in a topological order; this produces an acyclic rooted network with the same support tree. Applying it to a universal rooted network on $X \setminus \{x\}$ with $x$ attached above the root yields the universal unrooted network.

## Sources

- A. Francis, K. T. Huber, V. Moulton, "Tree-based unrooted phylogenetic networks", *Bulletin of Mathematical Biology* (2018), Sections 3–4 (Lemma 4, Theorems 2–4, Corollary 1), <https://doi.org/10.1007/s11538-017-0381-3> (PMC5790869).
