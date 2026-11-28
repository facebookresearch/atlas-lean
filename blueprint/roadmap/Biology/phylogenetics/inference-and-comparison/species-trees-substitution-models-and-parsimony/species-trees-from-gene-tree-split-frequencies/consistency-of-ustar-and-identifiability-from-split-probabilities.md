# Consistency of USTAR and identifiability from gene-tree split probabilities

Let $\sigma = (\psi,\lambda)$ be a binary species tree on taxa $\mathcal X$ with topology $\psi$ and internal edge lengths $\lambda$ (coalescent units), and let gene trees arise under the multispecies coalescent on $\sigma$. Give each edge of an unrooted topological gene tree $T$ length $1$ and let $D_T(a,b)$ be the number of edges on the path between leaves $a$ and $b$. For a distribution $\mu$ on gene trees, the **USTAR dissimilarity** is

$$D = \mathbb E_\mu(D_T) = \sum_T \mu(T)\, D_T,$$

estimated by the mean of the $D_T$ over a sample of gene trees. A USTAR method applies a tree-building method $M$ to $D$; with $M$ = neighbor joining this is $\mathrm{NJ}_{st}$.

**Theorem.**

1. (Exact fit) Under the multispecies coalescent on $\sigma$, $D = \mathbb E_\sigma(D_T)$ is a tree metric whose tree has the unrooted topology of $\psi$.
2. (Consistency) If $M$ returns the unique tree fitting any tree metric and is continuous at tree metrics of binary trees, then USTAR/$M$ is a statistically consistent estimator of the unrooted species tree topology from gene trees. This covers neighbor joining, so $\mathrm{NJ}_{st}$ is consistent for any number of taxa.
3. (Splits suffice) For any gene-tree distribution $\mu$, the split probabilities $\mathbb P_\mu(A \mid B)$ over all bipartitions $A \mid B$ of the leaf set determine $\mathbb E_\mu(D_T)$.
4. (Identifiability) Consequently the unrooted species tree topology is identifiable from gene-tree split probabilities under the multispecies coalescent.

## Expansion

Rooting each gene tree splits its internode distances into internal and pendant parts, giving $D_T = D^r_{T^r} + D^{up}_T - D^{rp}_{T^r}$, where $D^r_{T^r}$ is the rooted STAR distance. The expected STAR distances fit the species tree, and the correction terms are leaf-additive, so the expected USTAR dissimilarity still satisfies the four-point condition with the splits of $\psi$. Continuity of $M$ at binary tree metrics and the law of large numbers for the empirical mean of $D_T$ then give consistency. For item 3, every edge of $T$ is a split, so for $a \ne b$, $D_T(a,b) = 2 + \#\{\text{nontrivial splits of } T \text{ separating } a \text{ and } b\}$; taking expectations writes $D$ as a linear function of the split probabilities.

## Sources

- Elizabeth S. Allman, James H. Degnan, John A. Rhodes, "Species Tree Inference from Gene Splits by Unrooted STAR Methods", IEEE/ACM Transactions on Computational Biology and Bioinformatics 15 (2018), 337–342, <https://doi.org/10.1109/tcbb.2016.2604812>. Published version of arXiv:1604.05364, cited next; locators there refer to the arXiv version.
- Elizabeth S. Allman, James H. Degnan, John A. Rhodes, "Species tree inference from gene splits by Unrooted STAR methods", arXiv (2016). Section 3, Theorems 4.1–4.2, Theorem 5.1, Corollary 5.2. <https://doi.org/10.48550/arXiv.1604.05364>
