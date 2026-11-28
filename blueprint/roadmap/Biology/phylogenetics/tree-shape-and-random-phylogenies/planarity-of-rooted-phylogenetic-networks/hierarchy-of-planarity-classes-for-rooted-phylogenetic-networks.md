# Hierarchy of planarity classes for rooted phylogenetic networks

**Definitions.** A *rooted phylogenetic network* on a finite set $X$ is an acyclic digraph with a single source $\rho$ (the root), sink set $X$, and no vertex of in-degree $1$ and out-degree $1$. It is *planar*, *upward planar* (planar drawing with every arc pointing upward) or *outer planar* if the digraph is. It is *terminal planar* if it has a planar drawing with the root and all leaves on the outer face. Write $\mathcal{P}_p(X) \supseteq \mathcal{P}_u(X)$, $\mathcal{P}_t(X)$, $\mathcal{P}_o(X)$ for these classes. A binary network is *level-$k$* if it becomes a tree after deleting at most $k$ arcs from each biconnected component; $\mathcal{L}_k(X)$ is the class of level-$k$ networks. The *completion* $N^*$ adds one new vertex $t$ and arcs $x \to t$ for all $x \in X$.

**Theorem.**
1. $N$ is terminal planar if and only if its completion $N^*$ is upward planar.
2. For every $X$ with $|X| \ge 2$,

$$\mathcal{P}_o(X) \subsetneq \mathcal{P}_t(X) \subsetneq \mathcal{P}_u(X) \subsetneq \mathcal{P}_p(X).$$

3. Each of the four properties can be decided, and a corresponding drawing produced, in $O(m)$ time for a network with $m$ vertices; hence in $O(|X|)$ time for binary reticulation-visible networks and $O(|X|^2)$ time for normal networks.
4. *Level-$k$ networks.* $\mathcal{L}_1(X) \subseteq \mathcal{P}_o(X)$; $\mathcal{L}_2(X) \subseteq \mathcal{P}_u(X)$ but $\mathcal{L}_2(X) \not\subseteq \mathcal{P}_t(X)$; $\mathcal{L}_3(X) \subseteq \mathcal{P}_p(X)$ but $\mathcal{L}_3(X) \not\subseteq \mathcal{P}_u(X)$; and $\mathcal{L}_4(X) \not\subseteq \mathcal{P}_p(X)$.
5. For a level-2 network $N$ the following are equivalent: $N$ is terminal planar; $N$ is outer planar; $N$ contains no subdivision of four explicit small digraphs; the underlying graph $U(N)$ contains no subdivision of $K_{2,3}$.

## Proof sketch

Joining all leaves to a common sink turns "root and leaves on one face" into a single-source, single-sink condition, and for such $st$-digraphs upward planarity is equivalent to planarity with $s$ and $t$ on a common face; this gives item 1 and, with linear-time upward-planarity testing for single-source digraphs and linear-time planarity tests, item 3. Strictness in item 2 is witnessed by small networks on two leaves. For level-$k$ networks every biconnected component has bounded cyclomatic number, and planarity (respectively upward planarity) holds iff it holds for each biconnected component, so the level bounds reduce to a finite case analysis; the level-4 counterexample contains a subdivision of $K_{3,3}$.

## Sources

- Vincent Moulton and Taoyang Wu, "Planar Rooted Phylogenetic Networks", *IEEE/ACM Transactions on Computational Biology and Bioinformatics* 20 (2023), 1289–1297, <https://doi.org/10.1109/tcbb.2022.3185670>. Preprint version: arXiv:2203.10156 (2022), Theorems 3.1, 3.2, 3.3, 4.1 and 4.2, <https://doi.org/10.48550/arXiv.2203.10156>.
