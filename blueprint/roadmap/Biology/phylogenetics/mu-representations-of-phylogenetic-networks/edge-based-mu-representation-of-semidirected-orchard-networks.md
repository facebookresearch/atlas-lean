# Edge-based μ-representation of semidirected orchard networks

A **semidirected network** keeps the direction of hybrid edges but forgets the root position and the direction of tree edges; it is the identifiable object under many network inference models. Formally, an **$\mathcal L$-network** $N$ is a semidirected acyclic graph (edges $E=E_U\sqcup E_D$, undirected and directed) whose leaves are tree nodes, with an injection of its leaves into a fixed taxon set $\mathcal L=[n]$; it has **root components** (maximal undirected regions where the root may lie), hybrid nodes (in-degree 2) and tree nodes. $N$ is **orchard** if it can be reduced to a trivial forest by repeatedly reducing **cherries**: tree cherries $(a,b)$ with a common parent, and reticulate cherries $(a,b)$ where the parent of $a$ is a hybrid node with the parent of $b$ among its parents.

**Edge-based μ-vectors.** For an edge $e$ with endpoints $u,v$, let $\mu_i(e,v)$ ($i\in[n]$) be the number of semidirected paths from $v$ to leaf $i$ avoiding $e$, and $\mu_0(e,v)$ the number of such paths from $v$ to hybrid nodes. The simple μ-vector is $\mu(e,v)=(\mu_0(e,v),\dots,\mu_n(e,v))$. Each edge $e$ and each root component $T$ receive a **μ-entry**: a multiset of one or two **tagged** μ-vectors with tags tree edge, hybrid edge, root node, or a new tag marking edges admissible to an unresolved root component (Definitions 8 and 9 of the source; for a directed edge $u\to v$ outside such components the entry is $\{(\mu(e,v),t)\}$ with $t$ the hybrid tag iff $v$ is hybrid). The **edge-based μ-representation** $\mu(N)$ is the multiset of all these entries.

**Theorem (encoding).** If $N_1,N_2$ are binary orchard $\mathcal L$-networks, then $N_1\cong N_2$ if and only if $\mu(N_1)=\mu(N_2)$. Moreover, an explicit algorithm that repeatedly detects and reduces cherries directly on a μ-representation terminates on every orchard representation $\boldsymbol\mu$ and reconstructs an orchard network $N$ with $\mu(N)=\boldsymbol\mu$; applied to $\mu(N)$ for arbitrary $N$, it decides whether $N$ is orchard (it gets stuck with no cherry before reaching a trivial forest iff $N$ is not orchard).

**Theorem (distance).** For a fixed taxon set $\mathcal L$, the edge-based μ-dissimilarity

$$d_\mu(N_1,N_2)=\left|\mu(N_1)\,\triangle\,\mu(N_2)\right|$$

(symmetric difference of multisets) is a metric on binary orchard $\mathcal L$-networks and is computable in polynomial time.

## Depends on

- [Tree-child μ-compatibility characterizes μ-representations of tree-child networks](tree-child-mu-compatibility.md)

## Expansion

The engine is that reducing a cherry commutes with taking μ-representations: cherries of every type (tree or reticulate, and four positional types relative to root components and undirected edges) can be read off from multiplicities and tags in $\mu(N)$, and $\mu(N^{(a,b)})=\mu(N)^{(a,b)}$ for an explicit multiset operation. Cherry reduction preserves the orchard property, and each reduction is inverted by a typed cherry addition, so induction on the length of a complete reduction sequence gives both reconstruction and uniqueness. Path counts are additive across an edge, $m(u,x)=m(u,x;e)+m(v,x;e)$, which makes the entry of a root component independent of which admissible edge is used. The hybrid-count coordinate $\mu_0$ and the extra tag resolve the cases (parallel hybrid edges, unresolved roots) where earlier edge-based semidirected representations fail to separate networks; for non-orchard networks the representation can collide, so the metric property is specific to the orchard class.

## Sources

- G. Ribas, J. C. Pons, C. Ané, "A μ-distance for semidirected orchard phylogenetic networks", arXiv:2605.06243 (2026), Section 2 (Lemma 1, Propositions 4-6), Section 3 (Definitions 8-9, Propositions 10 and 13, Corollary 14) and Section 4 (Theorem 15, Corollary 17, Definition 15, Theorem 18), <https://doi.org/10.48550/arXiv.2605.06243>.
