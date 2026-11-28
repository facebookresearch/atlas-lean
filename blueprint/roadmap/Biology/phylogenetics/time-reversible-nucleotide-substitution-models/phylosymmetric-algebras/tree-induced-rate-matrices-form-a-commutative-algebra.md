# Tree-induced rate matrices form a commutative algebra

**Construction.** Let $\mathcal T$ be a rooted tree whose $n$ leaves are the character states (e.g. amino acids), and assign a rate $\omega(u)$ to each non-leaf vertex $u$. The rate of change between states $x\ne y$ is the rate at their most recent common ancestor, $\omega(\mathrm{mrca}(x,y))$. For a rate value $\alpha=\omega(u)$, the **$\alpha$-mrca graph** $G_\alpha$ has an edge $\{x,y\}$ iff $\omega(\mathrm{mrca}(x,y))=\alpha$; it is a complete multipartite graph on the leaves below $u$ (one part per child of $u$) plus isolated vertices. Set

$$Q_\alpha=-L(G_\alpha)=A(G_\alpha)-D(G_\alpha),$$

minus the graph Laplacian, so the rate matrix of the model is $Q=\sum_\alpha\alpha Q_\alpha$. The **phylosymmetric algebra** is $\mathcal Q_{\mathcal T}=\operatorname{span}_{\mathbb R}\{Q_\alpha\}$. Hierarchies on $X$ (equivalently rooted trees) are in bijection with such tree-induced graph sets.

**Theorem (products).** Let $u,v$ be non-leaf vertices with rates $\alpha,\beta$, let $T^\alpha$ be the subtree at $u$ and $|T|$ its number of leaves.

*(1)* If $v$ is a descendant of $u$ and $T^\alpha_\beta$ is the subtree at the child of $u$ that is an ancestor of $v$, then

$$Q_\alpha Q_\beta=\big(|T^\alpha_\beta|-|T^\alpha|\big)Q_\beta=Q_\beta Q_\alpha.$$

*(2)* If $u$ and $v$ are incomparable, then $Q_\alpha Q_\beta=0$.

*(3)* $(Q_\alpha^2)_{ii}=d_i(d_i+1)$, $(Q_\alpha^2)_{ij}=-|T^\alpha|$ if $i,j$ lie in different parts of $G_\alpha$, and $(Q_\alpha^2)_{ij}=d_i$ if $i\ne j$ lie in the same part, where $d_i$ is the degree of $i$ in $G_\alpha$.

Consequently, for a binary tree with distinct rates, $\mathcal Q_{\mathcal T}$ is a commutative matrix algebra; the transition matrices $e^{tQ}$ then lie in $I+\mathcal Q_{\mathcal T}$ and can be written in closed form without numerical matrix exponentials.

**Theorem (equal rates).** Setting $\alpha=\beta$ for two internal vertices $u,v$ keeps the matrix set closed under multiplication if and only if $u$ is the parent of $v$ (or vice versa), or $u,v$ are siblings with the same number of leaf descendants.

## Expansion

Since $Q_\alpha$ is symmetric, products are computed by counting walks in the union of the two mrca graphs: an edge of $G_\beta$ inside one child subtree of $u$ followed by an edge of $G_\alpha$ leaving that subtree, minus degree corrections, which collapses to a multiple of $Q_\beta$. Incomparable vertices have mrca graphs on disjoint leaf sets, so their Laplacians multiply to zero. Symmetric matrices whose product is symmetric commute, which gives commutativity. Merging a parent and child rate is the same as contracting the edge between them, which yields another tree and hence another phylosymmetric algebra; sibling merges stay closed only when the two subtrees have equal size, because only then does the product formula produce a multiple of the merged generator.

## Sources

- Michael Hendriksen, Julia A. Shore, "Phylosymmetric algebras: mathematical properties of a new tool in phylogenetics", arXiv:2009.11599 (2020), Theorems 1, 2 and 5–11, <https://doi.org/10.48550/arXiv.2009.11599>.
