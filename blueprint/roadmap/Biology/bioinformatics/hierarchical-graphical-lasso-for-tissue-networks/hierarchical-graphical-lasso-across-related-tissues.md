# Hierarchical graphical lasso across related tissues

Let tissues $k = 1, \dots, K$ have $n^{(k)}$ samples of $p$ Gaussianized gene expression levels with empirical covariance $\Sigma^{(k)}$, and let a rooted binary tree have these tissues as leaves and internal nodes $K + 1, \dots, 2K - 1$ (built, for example, by agglomerative clustering of mean expression profiles); write $p(k)$ for the parent of node $k$. The network algorithm GNAT estimates one precision matrix $S^{(k)}$ per node by

$$\max_{S^{(1)}, \dots, S^{(2K-1)}} \; \sum_{k=1}^{K} \Big( \frac{n^{(k)}}{2}\big(\log\det S^{(k)} - \operatorname{tr}(S^{(k)} \Sigma^{(k)})\big) - \lambda_s^{(k)} \lVert S^{(k)} \rVert_1 \Big) - \lambda_p \sum_{k=1}^{2K-2} \lVert S^{(k)} - S^{(p(k))} \rVert_2^2,$$

subject to $S^{(k)} \succeq 0$ for the leaves, where $\lVert \cdot \rVert_1$ is the entrywise $\ell_1$ norm of the off-diagonal entries, $\lVert\cdot\rVert_2^2$ the sum of squared entries, $\lambda_s^{(k)} > 0$ tissue-specific sparsity parameters and $\lambda_p > 0$ the parent-similarity weight. Zero entries of $S^{(k)}$ encode conditional independence of two genes given all others in tissue $k$. The objective is concave; it is maximized by initializing each leaf with the graphical lasso for its own data and then alternating between updating all internal nodes with the leaves fixed (in closed form) and updating the leaves in parallel with the internal nodes fixed.

## Depends on

- [Internal nodes of the hierarchy are averages of their neighbours](internal-nodes-are-averages-of-their-neighbours.md)

## Expansion

Each leaf term is the Gaussian log-likelihood of a precision matrix plus a lasso penalty, i.e. a graphical lasso problem; internal nodes carry no data and act as latent shared networks. The squared penalty along tree edges shrinks closely related tissues toward a common network, which matters for tissues with few samples (about two dozen per brain region in the GTEx data used) whose networks would otherwise be unidentifiable. Choosing a squared rather than an $\ell_1$ coupling makes the internal-node step quadratic and lets the leaf problems decouple given their parents. The sparsity parameters were set by a heuristic matching the $\ell_1$ penalty to the BIC penalty, $\lambda_s^{(k)} \approx \log(n^{(k)})/\bar s$ with $\bar s$ the mean magnitude of nonzero off-diagonal precision entries, calibrated on a few tissues and extrapolated by regression on $\log(n^{(k)})/\bar\Sigma^{(k)}$; for $p \approx 10^4$ genes, the problem was split into approximate blocks of at most $500$ genes by an eigenvector partition of $\sum_k n^{(k)} C^{(k)}$ with $C^{(k)}_{ij} = \max(0, \Sigma^{(k)}_{ij} - \lambda_s^{(k)})^2$.

## Sources

- E. Pierson, D. Koller, A. Battle, S. Mostafavi et al. (GTEx Consortium), "Sharing and specificity of co-expression networks across 35 human tissues", PLoS Computational Biology 11 (2015), e1004220, <https://doi.org/10.1371/journal.pcbi.1004220> (PMC4430528). Results (Algorithm) and Materials and Methods.
