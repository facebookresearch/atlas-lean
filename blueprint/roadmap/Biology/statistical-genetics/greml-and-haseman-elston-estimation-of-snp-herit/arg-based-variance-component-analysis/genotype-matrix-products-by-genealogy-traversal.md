# Genotype-matrix products by traversal of a genealogy

Let $T$ be a rooted tree (a marginal tree of an ancestral recombination graph, ARG) whose leaves are $n$ sampled haplotypes, and let $p$ mutations be placed on its edges, mutation $j$ on edge $e_j$. Under the infinite-sites model the haploid genotype matrix $X \in \{0,1\}^{n \times p}$ has $X_{ij} = 1$ exactly when leaf $i$ lies below $e_j$. For a vector $u \in \mathbb R^n$ and a vector $v \in \mathbb R^p$:

1. **Left product.** $(u^\top X)_j = S(c_j)$, where $c_j$ is the child endpoint of $e_j$ and $S(\nu) = \sum_{\text{leaves } i \text{ below } \nu} u_i$. The subtree sums satisfy $S(\nu) = u_\nu$ at a leaf and $S(\nu) = \sum_{\text{children } \kappa \text{ of } \nu} S(\kappa)$ otherwise, so one post-order traversal computes $u^\top X$.
2. **Right product.** $(Xv)_i = P(i)$, where $P(\nu) = \sum_{j : e_j \text{ on the path from the root to } \nu} v_j$. These path sums satisfy $P(\text{root}) = 0$ and $P(\kappa) = P(\nu) + \sum_{j : e_j = (\nu,\kappa)} v_j$, so one pre-order traversal computes $Xv$.

Each product costs $O(|T| + p)$ operations, where $|T| \le 2n - 1$ is the number of nodes, instead of $O(\mathrm{nnz}(X))$, which can be as large as $np$. Along a chromosome, consecutive marginal trees of an ARG differ by few edges, and subtree sums of unchanged subtrees can be reused, so the cost over a region grows with the number of distinct ARG edges rather than with the total number of carrier entries. Column centring and scaling cost nothing extra: for $Z = (X - \mathbf 1 \mu^\top) D^{-1}$ with allele frequencies $\mu$ and diagonal scales $D$, $Zv = X(D^{-1}v) - \mathbf 1\,(\mu^\top D^{-1} v)$ and $u^\top Z = (u^\top X - (u^\top \mathbf 1)\mu^\top) D^{-1}$; diploid individuals are handled by summing the rows of their two haplotypes.

## Depends on

- [Minimal descriptor of an ancestral recombination graph](../../../coalescent-theory/two-locus-coalescent/minimal-descriptors-of-ancestral-recombination-graphs/minimal-descriptor-of-an-ancestral-recombination-graph.md): an ARG as the union of its embedded marginal trees
- [Standardized genotype matrix](../../ld-score-regression/is-standardized.md): the centred and scaled matrix $Z$

## Expansion

Carriers of a mutation are exactly the descendants of its edge, so a column of $X$ is the indicator of a subtree and a row is the indicator of a root-to-leaf path. Memoising subtree sums and path sums replaces repeated scans of overlapping carrier sets, which is where linkage disequilibrium makes dense products wasteful. Products with $X$ and $X^\top$ are all that iterative numerical routines need: Hutchinson's trace estimator for $\operatorname{tr}(R^2)$, randomized singular value decomposition for leading eigenvalues of the relationship matrix $R \propto ZZ^\top$, and conjugate gradients for solving $(\sigma_g^2 R + \sigma_e^2 I)x = y$ in best linear unbiased prediction and mixed-model association. Zhu et al. call this ARG-matrix multiplication and report sublinear scaling in sample size on 5-Mb simulated regions, speedups of more than $15\times$ over optimized dense libraries near $500{,}000$ individuals, and a $\sim 15\times$ speedup for the top 20 principal components of $1{,}000{,}000$ samples relative to the same randomized algorithm in PLINK2.

## Sources

- J. Zhu, G. Kalantzis, A. Pazokitoroudi, Á. F. Gunnarsson, H. Loya, H. Chen, S. Sankararaman, P. F. Palamara, "Leveraging ancestral recombination graphs for scalable mixed-model analysis of complex traits", Cell Genomics (2026), <https://doi.org/10.1016/j.xgen.2025.101072> (PMC12903391), STAR Methods, "ARG-matrix multiplication and ARG-RHE", and Results, "Scalability of ARG-matrix multiplication".
- P. Ralph, K. Thornton, J. Kelleher, "Efficiently summarizing relationships in large samples: a general duality between statistics of genealogies and genomes", Genetics 215 (2020), 779–797, <https://doi.org/10.1534/genetics.120.303253>.
