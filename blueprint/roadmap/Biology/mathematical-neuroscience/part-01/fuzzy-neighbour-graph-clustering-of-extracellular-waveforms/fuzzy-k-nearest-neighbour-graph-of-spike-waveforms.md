# Fuzzy $k$-nearest-neighbour graph of spike waveforms

Let $x_1,\dots,x_N$ be normalized, trough-aligned average extracellular action-potential waveforms of single units, $d$ a metric on waveform space, $k \ge 3$ an integer and $x_{i1},\dots,x_{ik}$ the $k$ nearest neighbours of $x_i$. Assume that, for each $i$, at least one of these neighbours lies at positive distance from $x_i$, and that fewer than $\log_2 k$ of them lie within distance $\rho_i$, where

$$\rho_i = \min\{d(x_i, x_{ij}) : 1 \le j \le k,\ d(x_i,x_{ij}) > 0\}.$$

Then the function

$$\sigma \mapsto \sum_{j=1}^k \exp\!\left(-\frac{\max(0, d(x_i,x_{ij}) - \rho_i)}{\sigma}\right)$$

increases strictly and continuously on $(0, \infty)$ from the number of neighbours within distance $\rho_i$ (as $\sigma \to 0^+$) towards $k$ (as $\sigma \to \infty$), so there is a unique $\sigma_i > 0$ at which it equals $\log_2 k$. (Without the assumption the scale need not exist: if all $k$ neighbour distances are equal and positive, the sum is identically $k$.) Define directed edge weights $a_{ij} = \exp\bigl(-\max(0, d(x_i,x_j) - \rho_i)/\sigma_i\bigr)$ for $x_j$ among the $k$ neighbours of $x_i$ and $a_{ij} = 0$ otherwise, and the symmetrized graph by the probabilistic union

$$B = A + A^{\top} - A \circ A^{\top}, \qquad b_{ij} = 1 - (1-a_{ij})(1-a_{ji}),$$

with $\circ$ the entrywise product. Then $B$ is symmetric with entries in $[0,1]$, $b_{ij} \ge \max(a_{ij}, a_{ji})$, and every point is joined to at least one other point, a nearest neighbour at positive distance, by an edge of weight $1$. The graph $B$ need not be connected: two well-separated groups of more than $k$ points each can have all their $k$ nearest neighbours inside their own group. Community detection on $B$ by modularity maximization (Louvain) partitions the units into putative cell types; a low-dimensional embedding of the same graph is used only for display, so the clusters do not depend on the layout.

## Expansion

The local scale $\rho_i$ rescales distances so that each point sees its nearest neighbour at distance zero, which gives every point, including points in sparse regions, at least one edge of weight $1$, and $\sigma_i$ fixes the effective number of neighbours at $\log_2 k$ regardless of local density. Strict monotonicity of $\sigma \mapsto e^{-c/\sigma}$ for $c > 0$, applied to the neighbours farther than $\rho_i$, and the intermediate value theorem give existence and uniqueness of $\sigma_i$ under the stated assumption. Writing $b_{ij} = 1-(1-a_{ij})(1-a_{ji})$ shows that $b_{ij}$ is the probability that at least one of two independent edges with probabilities $a_{ij}$ and $a_{ji}$ is present, hence lies in $[0,1]$ and dominates both. This is the graph construction of UMAP; the paper applies it to waveform shapes and reports eight stable clusters in macaque premotor cortex.

## Sources

- E. K. Lee, H. Balasubramanian, A. Tsolias, S. U. Anakwe, M. Medalla, K. V. Shenoy and C. Chandrasekaran, "Non-linear dimensionality reduction on extracellular waveforms reveals cell type diversity in premotor cortex", eLife 10 (2021), e67490, <https://doi.org/10.7554/eLife.67490>, PMCID PMC8452311. Methods, sections on graph construction and Louvain community detection. The paper writes the edge weight as a sum over neighbours; the per-edge form above is the one used to build $A$.
