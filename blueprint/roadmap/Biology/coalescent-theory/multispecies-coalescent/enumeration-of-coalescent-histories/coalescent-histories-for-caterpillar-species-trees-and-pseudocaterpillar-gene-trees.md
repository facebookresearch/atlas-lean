# Coalescent histories for caterpillar species trees and pseudocaterpillar gene trees

**Coalescent histories.** For a gene tree topology $G$ and a species tree $S$ on the same $n$ labeled taxa, a *coalescent history* is a map from the internal nodes of $G$ to the edges of $S$ (including the root edge above the species-tree root) that records where each coalescence can occur under the multispecies coalescent: each gene-tree node must map to an edge at or above the most recent common ancestor in $S$ of its descendant labels, and the map must be monotone along root-ward paths of $G$. Coalescent histories index the terms of the sum giving gene tree probabilities.

**Trees.** A *caterpillar* has a single cherry. A *generalized pseudocaterpillar* has exactly two cherries and every internal node has a child with at most two descendant leaves; labeling leaves left to right with the caterpillar's cherry on the left, it is a *$p$-pseudocaterpillar* ($4 \le p \le n$) when the second leaf of its second cherry has label $p$. With the Catalan triangle entries $C(n,k) = \binom{n+k}{k} - \binom{n+k}{k-1}$ for $1 \le k \le n$, $C(n,0) = 1$ and $C(n,k) = 0$ for $k>n$:

**Theorem.** Let $S$ be a caterpillar species tree with $n \ge 4$ leaves and $G$ an identically labeled $p$-pseudocaterpillar gene tree, $4 \le p \le n$. The number of coalescent histories of $(G,S)$ is

$$h(n,p) = \sum_{k=p-1}^{n-1} C(k,p-3)\,(k-p+2)\,C(n-p,\,n-k-1).$$

Among all labelings of a $p$-pseudocaterpillar gene tree, $h(n,p)$ is the maximum, attained exactly when $G$ and $S$ are identically labeled. Extending the formula to $p=3$ gives $h(n,3) = \dfrac{3\,(2n-4)!}{n!\,(n-3)!}$.

**Theorem (symmetry and maximum).** For $3 \le p \le n$, $h(n,p) = h(n,n-p+3)$. The maximizing position is $p_m = (n+3)/2$ for odd $n$, and the two adjacent positions $(n+2)/2$ and $(n+4)/2$ for even $n$. The maximum exceeds the caterpillar–caterpillar count $\mathcal C_{n-1}$ (the Catalan number) for odd $n \ge 7$ and even $n \ge 8$, and $h(n,p_m)$ has exponential order $4$, the same as $\mathcal C_n$.

## Depends on

- [Rooted binary species tree with branch lengths](../species-tree.md)
- [The multispecies coalescent](../gene-tree-prob.md)

## Proof depends on

## Expansion

In a caterpillar species tree, the edges available to a gene-tree node form a nested chain, so a coalescent history of the left caterpillar part is a monotone lattice path below a diagonal, counted by a Catalan triangle entry; the second cherry contributes a second, independent lattice path, and the factor $(k-p+2)$ counts placements of the node joining them. Summing over the edge $k$ that receives the junction node gives $h(n,p)$. The symmetry $p \leftrightarrow n-p+3$ exchanges the roles of the two paths, which puts the maximum near the middle.

## Sources

- Egor Alimpiev and Noah A. Rosenberg, "Enumeration of coalescent histories for caterpillar species trees and $p$-pseudocaterpillar gene trees", arXiv:2103.13464 (2021), Definition of generalized pseudocaterpillars, Theorem 4, Propositions 5, 6, 12 and 13, Theorems 7 and 14, <https://doi.org/10.48550/arXiv.2103.13464>; published in *Advances in Applied Mathematics* 131 (2021), article 102265, <https://doi.org/10.1016/j.aam.2021.102265>. Locators follow arXiv v1.
