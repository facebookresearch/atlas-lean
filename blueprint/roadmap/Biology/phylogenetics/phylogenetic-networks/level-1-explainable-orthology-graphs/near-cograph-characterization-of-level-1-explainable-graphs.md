# Near-cograph characterization of level-1 explainable graphs

**Networks.** A *network* on a leaf set $X$ is a DAG $N$ with a unique root; it is *phylogenetic* if no vertex has out-degree $1$ and in-degree at most $1$. A *block* is a maximal biconnected subgraph; $N$ is *level-$k$* if every block $B$ contains at most $k$ hybrid vertices other than its unique maximal vertex $\max_B$. $N$ has the *2-lca property* if every pair $x, y \in X$ has a unique lowest common ancestor $\mathrm{lca}_N(x,y)$.

**Explained graphs.** Let $t : V^0(N) \to \{0,1\}$ label the inner vertices of a network $N$ with the 2-lca property. The graph $\mathscr G(N,t) = (X,E)$ has $\{x,y\} \in E$ if and only if $t(\mathrm{lca}_N(x,y)) = 1$; a graph $G$ is *explained* by $(N,t)$ if $G = \mathscr G(N,t)$. Reading $X$ as genes, label $1$ as speciation and label $0$ as duplication, $\mathscr G(N,t)$ is the orthology graph predicted by the labeled network. A graph is *Lev-1-Ex* if some $0/1$-labeled level-1 network explains it.

**Near-cographs and primitive graphs.** A *cograph* is a graph with no induced path $P_4$. A graph $G = (V,E)$ is a *near-cograph* if $|V| = 1$ or $G - v$ is a cograph for some vertex $v$. A graph is *primitive* if it has at least four vertices and only trivial modules (vertex sets $M$ such that every vertex outside $M$ is adjacent to all or none of $M$).

**Theorem 4.12.** A primitive graph is Lev-1-Ex if and only if it is a near-cograph.

**Theorem 4.19.** A graph $G$ is Lev-1-Ex if and only if, for every non-trivial prime module $M$ of $G$, the quotient graph $G[M]/\mathbb M_{\max}(G[M])$ by the maximal strong submodules is a near-cograph.

**Theorem 4.20.** Equivalently, $G$ is Lev-1-Ex if and only if every primitive induced subgraph of $G$ is a near-cograph.

**Theorem 4.21.** A graph is Lev-1-Ex if and only if it is explained by a *phylogenetic* $0/1$-labeled level-1 network.

**Theorem 4.22.** Whether a graph $G = (X,E)$ is explained by some labeled level-1 network can be decided in $O(|X| + |E|)$ time, and in the affirmative case an explaining $0/1$-labeled level-1 network is constructed within the same time bound.

Since every cograph has no prime modules, the theorems contain the classical fact that cographs are exactly the graphs explained by labeled trees.

## Expansion

If a primitive graph is explained by a level-1 network, one can take the network to have a single non-trivial block whose unique hybrid is a leaf $z$ (Lemma 4.7); deleting $z$ leaves a tree explanation, so $G - z$ is a cograph. Conversely, if $G - z$ is a cograph explained by a labeled tree, grafting $z$ below a new hybrid vertex whose parents are placed so that the lowest common ancestors of $z$ with the other leaves carry the required labels yields a level-1 explanation (Theorem 3.9 and Corollary 4.11). For general graphs the modular decomposition tree is built, each prime vertex is replaced by a network explaining its quotient (a prime-vertex replacement network, Proposition 4.17 and Lemma 4.18), and level-1 is preserved when every quotient is a near-cograph. Linear time follows from linear-time modular decomposition and linear-time cograph recognition applied to each quotient.

## Sources

- A. Lindeberg, G. E. Scholz, N. Wieseke, M. Hellmuth, "Orthology and Near-Cographs in the Context of Phylogenetic Networks", *Algorithms for Molecular Biology* 20(1) (2025), 19, Definitions 2.2, 2.6, 3.1 and 4.8, Lemma 4.7, Corollary 4.11, Theorems 3.9, 4.12, 4.19, 4.20, 4.21 and 4.22, <https://doi.org/10.1186/s13015-025-00285-7> (preprint arXiv:2502.08746).
