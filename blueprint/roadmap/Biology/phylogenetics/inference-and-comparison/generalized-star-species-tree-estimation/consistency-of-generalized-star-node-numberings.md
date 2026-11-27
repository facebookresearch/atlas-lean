# Consistency of generalized STAR node numberings

Let $\sigma = (\psi,\lambda)$ be a rooted metric species tree on an $n$-taxon set $\mathcal{X}$, with topology $\psi$ and internal branch lengths $\lambda_i$ in coalescent units, and let rooted gene-tree topologies $T$ (one gene lineage per taxon) arise under the multispecies coalescent with probabilities $\mathbb{P}_\sigma(T)$. A **node numbering sequence** is $a_0 \ge a_1 \ge \cdots \ge a_{n-2} \ge a_{n-1} = 0$ with $a_\ell > a_{\ell+1}$ for some $\ell$; it assigns $a_i$ to every internal node of a gene tree at depth $i$ (number of edges from the root), and the gene tree is metrized ultrametrically with each node at height equal to its number, so that $D_T(x,y)$ is twice the number of the most recent common ancestor of $x$ and $y$. Standard STAR uses $a_i = n - i$. A matrix **strongly fits** a topology $\psi$ ultrametrically if it is the leaf-distance matrix of $\psi$ with some positive edge lengths forming an ultrametric tree (weakly fits: nonnegative edge lengths).

1. For every node numbering sequence and all $\lambda_i \in (0,\infty)$, the expected matrix

$$
\mathbb{E}_\sigma(D_T) = \sum_T \mathbb{P}_\sigma(T)\, D_T
$$

strongly fits $\psi$ ultrametrically (Theorem 3.2).

2. Consequently, a generalized STAR method (any such numbering, followed by any tree-selection method that returns a binary tree from a distance table strongly fitting it and is continuous at such tables, such as UPGMA or neighbor joining) is statistically consistent for the species tree topology $\psi$ when $\psi$ is binary and all $\lambda_i > 0$ (Corollary 3.3).

3. If the node numbering sequence is strictly decreasing, then $\mathbb{E}_\sigma(D_T)$ strongly fits $\psi$ ultrametrically for every $\psi$ and all $\lambda_i \in (0,\infty]$; if it is not strictly decreasing, there are a binary $\psi$ and $\lambda_i \in (0,\infty]$ for which $\mathbb{E}_\sigma(D_T)$ only weakly fits $\psi$ (Theorem 3.5).

## Depends on

- [The multispecies coalescent](../../../coalescent-theory/multispecies-coalescent/gene-tree-prob.md)

## Expansion

Equivalently one assigns edge lengths $b_i = a_{i-1} - a_i \ge 0$ to internal edges at depth $i$ and extends pendant edges to make the gene tree ultrametric. The key property is that a node's number depends only on its depth: under the multispecies coalescent, lineages from a species-tree clade tend to coalesce below lineages from outside it, so the expected depth of their gene-tree ancestor is larger and the expected distance smaller, uniformly in a way that reproduces the species-tree clades. The condition fails for numberings that depend on more than depth. With the descendant-count numbering (each node numbered by its number of leaf descendants), the five-taxon caterpillar species tree $((((a,b){:}x,c){:}y,d){:}z,e)$ with $x = z = \infty$ and $y = 0$ gives three equiprobable gene trees whose averaged distance matrix fits a tree topologically different from the species tree, even unrooted; by continuity the same failure occurs for large finite $x,z$ and small positive $y$ (Section 2).

## Sources

- Elizabeth S. Allman, James H. Degnan, John A. Rhodes, Species tree inference by the STAR method, and generalizations, arXiv:1204.4413 (2012). <https://doi.org/10.48550/arXiv.1204.4413>. Published version: Journal of Computational Biology 20(1) (2013), 50–61, <https://doi.org/10.1089/cmb.2012.0101>; locators above refer to the arXiv version.
