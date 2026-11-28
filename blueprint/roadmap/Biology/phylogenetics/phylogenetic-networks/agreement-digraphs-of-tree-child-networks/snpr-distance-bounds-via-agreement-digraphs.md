# SNPR distance bounds via agreement digraphs

**Definitions.** Let $\mathcal N,\mathcal N'$ be rooted binary tree-child networks on $X$ with root $\rho$ (every non-leaf vertex has a child that is a tree vertex or leaf). A collection $\mathcal D=\{D_\rho,D_1,\dots,D_k\}$ of leaf-labelled acyclic digraphs is a phylogenetic digraph of $\mathcal N$ if the leaf sets of its elements partition $X$, only $D_\rho$ contains $\rho$ (as an isolated vertex or the unique source, of out-degree one), and $\mathcal D$ has an embedding in $\mathcal N$. Growing the embedded pieces along edges of $\mathcal N$ gives an extension $\mathcal R$ of $\mathcal D$ in $\mathcal N$. The cut size $c_{\mathcal D}$ is the number of edges of $\mathcal N$ not in an extension; it does not depend on the extension chosen. $\mathcal D$ is an agreement digraph of $\mathcal N$ and $\mathcal N'$ if it is a phylogenetic digraph of both, and an agreement tree-child digraph if, in addition, it is tree-child. Let

$$m_{\rm tc}(\mathcal N,\mathcal N')=\min_{\mathcal D}\big(c_{\mathcal D}+c'_{\mathcal D}\big)$$

over agreement tree-child digraphs. An SNPR operation on a network either deletes or adds a reticulation edge, or prunes a subnetwork and regrafts it elsewhere. Let $d_{\rm tc}(\mathcal N,\mathcal N')$ be the minimum total weight of a sequence of SNPR operations transforming $\mathcal N$ into $\mathcal N'$ through tree-child networks, where adding or deleting a reticulation edge costs $1$ and a prune-and-regraft costs $2$.

**Theorem.** For binary tree-child networks $\mathcal N,\mathcal N'$ on $X$,

$$\tfrac12\,m_{\rm tc}(\mathcal N,\mathcal N')\ \le\ d_{\rm tc}(\mathcal N,\mathcal N')\ \le\ m_{\rm tc}(\mathcal N,\mathcal N').$$

When $\mathcal N,\mathcal N'$ are trees, agreement digraphs are agreement forests and $c_{\mathcal D}=c'_{\mathcal D}$ equals the number of non-root components, so the bounds relate to the classical characterization of the rSPR distance by maximum agreement forests.

## Expansion

The agreement digraph records what the two networks share: its elements embed in both, and the cut sizes count the edges each network has outside those common pieces. Removing those edges from $\mathcal N$ and adding those of $\mathcal N'$ transforms one into the other, which gives the upper bound once the edge operations are realized as SNPR moves through tree-child networks. Conversely, a weighted SNPR sequence of total weight $w$ leaves a common agreement tree-child digraph of cut size sum at most $2w$. For arbitrary rooted binary networks, the unweighted SNPR distance is known only to lie between the agreement distance and six times it.

## Sources

- S. Kelk, S. Linz, C. Semple, "Bounding the SNPR distance between two tree-child networks using generalised agreement forests", *The Electronic Journal of Combinatorics* 32(3) (2025), P3.46, Section 1 (main theorem and comparison with the bound $d_{\rm AD}\le d^*_{\rm SNPR}\le 6d_{\rm AD}$ for general networks), Section 2 (phylogenetic digraphs, extensions, cut size), <https://doi.org/10.37236/13976> (preprint arXiv:2503.09076).
