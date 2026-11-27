# Cophenetic vectors single out rooted phylogenetic trees

Let $S = \{1,\dots,n\}$ be a set of taxa. A **weighted phylogenetic tree** on $S$ is a rooted tree with positive arc weights whose nodes are partly labelled bijectively by $S$, with every leaf and every elementary (one-child) node labelled, except possibly an unlabelled elementary root; labelled internal nodes are **nested taxa**. Let $\delta_T(v)$ be the depth of node $v$ (weighted distance from the root). The **cophenetic value** of taxa $i, j$ is $\varphi_T(i,j) = \delta_T(\mathrm{LCA}_T(i,j))$, so $\varphi_T(i,i) = \delta_T(i)$, and the **cophenetic vector** is

$$\varphi(T) = \big(\varphi_T(i,j)\big)_{1 \le i \le j \le n} \in \mathbb{R}^{n(n+1)/2}.$$

**Theorem.** For weighted phylogenetic trees $T, T'$ on $S$ (nested taxa allowed), $\varphi(T) = \varphi(T')$ implies $T \cong T'$.

**Corollary.** For unweighted phylogenetic trees without nested taxa, the off-diagonal part $\tilde\varphi(T) = (\varphi_T(i,j))_{1 \le i < j \le n} \in \mathbb{R}^{n(n-1)/2}$ already determines $T$, because then $\delta_T(i) = 1 + \max_{j \ne i} \varphi_T(i,j)$.

Without the depths $\varphi_T(i,i)$, neither pendant arc weights nor whether a taxon is nested can be recovered. The vector $\varphi(T)$ is computable in optimal $O(n^2)$ time by one preorder (depths) and one postorder (LCA pairs) traversal.

## Depends on

- [Tree metrics](../../splits-compatibility-ultrametrics-and-upgma/is-tree-metric.md)

## Expansion

Add a new label $r$ at the root and view $T$ as an unrooted $X$-tree on $X = S \cup \{r\}$. Its path-length metric is determined by the cophenetic vector:

$$d(i, r) = \delta_T(i), \qquad d(i, j) = \delta_T(i) + \delta_T(j) - 2\varphi_T(i,j).$$

A weighted $X$-tree is uniquely determined by its tree metric (the classical tree-metric reconstruction theorem), and the root is recovered as the node labelled $r$, which proves the theorem. Since the map $\varphi$ is injective, any norm on $\mathbb{R}^{n(n+1)/2}$ induces a metric on tree space.

## Sources

- G. Cardona, A. Mir, F. Rosselló, L. Rotger and D. Sánchez, "Cophenetic metrics for phylogenetic trees, after Sokal and Rohlf", BMC Bioinformatics 14 (2013), 3, Theorem 1 and Corollary 1, <https://doi.org/10.1186/1471-2105-14-3>, PMCID: PMC3716993.
- R. R. Sokal and F. J. Rohlf, "The comparison of dendrograms by objective methods", Taxon 11 (1962), 33–40, <https://doi.org/10.2307/1217208>.
