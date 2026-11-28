# Tree-child and reticulation-visible stable networks via X-sets

**Setting.** Let $X$ be a finite set with $|X|\ge3$. A phylogenetic network $N$ on $X$ is a rooted DAG with leaf set $X$ in which non-leaf tree vertices have out-degree two and hybrid vertices (in-degree at least two) have out-degree one. Its **un-fold** $\mathcal U(N)=(M,\mu)$ is the multi-labelled tree (MUL-tree) whose vertices are the directed paths from the root of $N$ ending at tree vertices, with each leaf labelled by the endpoint of its path; the **fold-up** $F(\mathcal M)$ of a MUL-tree identifies vertices with isomorphic sub-MUL-trees. $N$ is **stable** if $F(\mathcal U(N))\cong N$. On $V(\mathcal M)$ let $u\sim v$ if $u=v$ or the sub-MUL-trees at $u$ and $v$ are isomorphic, with projection $p_{\mathcal M}:V(\mathcal M)\to V(\mathcal M)/\sim$; for stable $N$ there is a bijection $\kappa_N$ from the tree vertices of $N$ to $V(\mathcal U(N))/\sim$.

An **$X$-set** of $\mathcal M$ is a set $C$ of leaves containing exactly one leaf labelled $x$ for every $x\in X$. It spans a subtree $M_C^+$ (all vertices on paths from $r_C=\mathrm{lca}_M(C)$ to $C$), whose suppression is a phylogenetic tree $M_C$; a tree $T$ on $X$ is **endorsed** by $\mathcal M$ via $C$ if $T\cong M_C$. Write $\overline{\xi_C^+}=p_{\mathcal M}\circ\xi_C^+:V(M_C^+)\to V(\mathcal M)/\sim$ for the induced map. $N$ *displays* $T$ if a subgraph of $N$ is a subdivision of $T$. A vertex $w$ of $N$ is a **vertex-stable ancestor** of a leaf $x$ if $w$ lies on every directed path from the root to $x$. $N$ is *tree-child* if every non-leaf vertex has a child that is a tree vertex, *compressed* if no arc joins two hybrid vertices, and *reticulation-visible* if every hybrid vertex is a vertex-stable ancestor of some leaf. For an $X$-set $C$ of $\mathcal M$, let $V(\mathcal M)^C$ consist of $r_C$ and all vertices $v$ of $\mathcal M$ such that no vertex below $v$ is equivalent to $r_C$. A tree $T$ is *strongly displayed* by $N$ if it is displayed with the root of $T$ at the root of $N$.

**Lemma 6.1.** $N$ is tree-child if and only if every interior vertex is a vertex-stable ancestor of some leaf; equivalently, $N$ is compressed and every interior tree vertex is a vertex-stable ancestor of some leaf.

**Proposition 6.2.** For a stable $N$ and a tree vertex $v$, $v$ is a vertex-stable ancestor of some leaf if and only if for every $X$-set $C$ of $\mathcal M=\mathcal U(N)$ either $\kappa_N(v)\in\overline{\xi_C^+}(V(M_C^+))$ or $v$ is an ancestor of $\kappa_N^{-1}(\overline{r_C})$.

**Theorem 6.4.** Let $N$ be a stable phylogenetic network on $X$ and $\mathcal M=\mathcal U(N)$.

1. $N$ is tree-child if and only if $\overline{\xi_C^+}(V(M_C^+))=V(\mathcal M)^C/\sim$ for every $X$-set $C$.
2. $N$ is reticulation-visible if and only if, for every $X$-set $C$ and every non-root vertex $v$ of $\mathcal M$ whose parent $u$ satisfies $|p_{\mathcal M}(u)|<|p_{\mathcal M}(v)|$, one has $p_{\mathcal M}(v)\in\overline{\xi_C^+}(V(M_C^+))$.

**Corollary 6.5.** In a stable tree-child network every strongly displayed phylogenetic tree is a base tree.

## Proof depends on

- [Displayed and base trees of stable networks via X-sets](displayed-and-base-trees-of-stable-networks-via-x-sets.md)

## Expansion

A vertex-stable ancestor of $x$ is visited by every root-to-$x$ path, hence by the path chosen for $x$ in any $X$-set, unless the whole subtree spanned by $C$ hangs below it; this is the dichotomy of Proposition 6.2. Tree-child networks are those in which every vertex has such a leaf, so for every $X$-set the folded image of $M_C^+$ is everything that is not above the image of $r_C$. Jumps $|p_{\mathcal M}(u)|<|p_{\mathcal M}(v)|$ in the multiplicity of equivalence classes along a MUL-tree arc mark where a path enters a hybrid vertex, and visibility of that hybrid is equivalent to its class being hit by every $X$-set. When the root of a displayed tree is the network root, $V(\mathcal M)^C$ is all of $V(\mathcal M)$, so part 1 gives surjectivity and Theorem 5.1 makes the tree a base tree.

## Sources

- Katharina T. Huber and Guillaume E. Scholz, "Phylogenetic networks that are their own fold-ups", arXiv (2018), Section 6 "Stable phylogenetic networks that are tree-child or reticulation-visible" (Lemma 6.1, Proposition 6.2, Lemma 6.3, Theorem 6.4, Corollary 6.5), <https://doi.org/10.48550/arXiv.1804.01841> Published version: Advances in Applied Mathematics 113 (2020) 101959, <https://doi.org/10.1016/j.aam.2019.101959>.
