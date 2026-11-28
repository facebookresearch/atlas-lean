# Displayed and base trees of stable networks via X-sets

**Setting.** Let $X$ be a finite set with $|X|\ge3$. A phylogenetic network $N$ on $X$ is a rooted DAG with leaf set $X$ in which non-leaf tree vertices have out-degree two and hybrid vertices (in-degree at least two) have out-degree one. Its **un-fold** $\mathcal U(N)=(M,\mu)$ is the multi-labelled tree (MUL-tree) whose vertices are the directed paths from the root of $N$ ending at tree vertices, with each leaf labelled by the endpoint of its path; the **fold-up** $F(\mathcal M)$ of a MUL-tree identifies vertices with isomorphic sub-MUL-trees. $N$ is **stable** if $F(\mathcal U(N))\cong N$. On $V(\mathcal M)$ let $u\sim v$ if $u=v$ or the sub-MUL-trees at $u$ and $v$ are isomorphic, with projection $p_{\mathcal M}:V(\mathcal M)\to V(\mathcal M)/\sim$; for stable $N$ there is a bijection $\kappa_N$ from the tree vertices of $N$ to $V(\mathcal U(N))/\sim$.

An **$X$-set** of $\mathcal M$ is a set $C$ of leaves containing exactly one leaf labelled $x$ for every $x\in X$. It spans a subtree $M_C^+$ (all vertices on paths from $r_C=\mathrm{lca}_M(C)$ to $C$), whose suppression is a phylogenetic tree $M_C$; a tree $T$ on $X$ is **endorsed** by $\mathcal M$ via $C$ if $T\cong M_C$. Write $\overline{\xi_C^+}=p_{\mathcal M}\circ\xi_C^+:V(M_C^+)\to V(\mathcal M)/\sim$ for the induced map. $N$ *displays* $T$ if a subgraph of $N$ is a subdivision of $T$. A tree $T$ is a *base tree* of $N$ if $N$ is tree-based with base tree $T$, that is, some subdivision of $T$ is a spanning tree of $N$ with leaf set $X$.

**Lemma 4.1.** If $T$ is displayed by a phylogenetic network $N$, then $T$ is endorsed by $\mathcal U(N)$ via some $X$-set $C$, which can be chosen compatibly with the path map of the embedding. The converse fails: a tree may be endorsed by the un-fold without being displayed, because two leaf paths of the endorsed tree may pass through the same vertex of $N$.

**Theorem 4.2.** Let $N$ be a stable phylogenetic network on $X$ and $T$ a phylogenetic tree on $X$. Then $T$ is displayed by $N$ if and only if there is an $X$-set $C$ of $\mathcal U(N)$ that endorses $T$ such that $\overline{\xi_C^+}$ is injective.

**Theorem 5.1.** Let $N$ be a stable phylogenetic network on $X$ and $T$ a phylogenetic tree on $X$. Then $T$ is a base tree for $N$ if and only if there is an $X$-set $C$ of $\mathcal U(N)$ that endorses $T$ such that $\overline{\xi_C^+}$ is bijective.

Thus displaying and tree-basedness of a stable network become properties of leaf selections in a single MUL-tree: injectivity says the selected copies never reuse a vertex of $N$, and surjectivity says every tree vertex of $N$ is used.

## Expansion

Vertices of $\mathcal U(N)$ are root paths of $N$, and for a stable network two vertices are equivalent under $\sim$ exactly when their paths end at the same tree vertex of $N$ (Lemma 3.1). An $X$-set picks one root path per leaf; the subtree $M_C^+$ is then a union of root paths, and its image in $V(\mathcal M)/\sim\cong$ tree vertices of $N$ is the set of vertices these paths visit. If no two vertices of $M_C^+$ fold to the same vertex, the paths form an embedded subdivision of $M_C$ in $N$; conversely an embedding gives such paths. If in addition every tree vertex is visited, the embedded tree spans $N$ and so is a support tree, the hybrid vertices being covered by the incoming arcs of the chosen paths.

## Sources

- Katharina T. Huber and Guillaume E. Scholz, "Phylogenetic networks that are their own fold-ups", arXiv (2018), Section 3 (Lemma 3.1), Section 4 "Displaying and endorsing phylogenetic trees" (Lemma 4.1, Theorem 4.2) and Section 5 "Stable phylogenetic networks that are tree-based" (Theorem 5.1), <https://doi.org/10.48550/arXiv.1804.01841> Published version: Advances in Applied Mathematics 113 (2020) 101959, <https://doi.org/10.1016/j.aam.2019.101959>.
