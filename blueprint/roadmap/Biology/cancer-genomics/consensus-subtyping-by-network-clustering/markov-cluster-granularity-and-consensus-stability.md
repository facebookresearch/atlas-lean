# Markov cluster granularity and consensus stability

Let $G$ be a weighted graph on $K$ vertices with non-negative adjacency matrix $W$ in which every vertex has at least one edge. The Markov cluster algorithm first adds a self-loop to every vertex (a positive diagonal), forms the column-stochastic transition matrix $P_{kl} = W_{kl}/\sum_{m} W_{ml}$, and then, with expansion power $e \ge 2$ and inflation parameter $f > 1$, iterates

$$P \leftarrow P^{e}, \qquad P_{kl} \leftarrow \frac{(P_{kl})^{f}}{\sum_{m} (P_{ml})^{f}},$$

until the change between successive matrices falls below a tolerance or an iteration limit is reached. The clusters are read from the final matrix: each vertex joins the cluster of the attractor rows that carry the mass of its column. With self-loops the iteration is observed to converge in practice, typically to an idempotent matrix, but convergence is not guaranteed for every non-negative input: without the self-loops, a single edge between two vertices gives the swap matrix $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, which expansion with $e = 3$ and inflation both leave unchanged, although its square is the identity, so the iteration stops at a matrix that is not idempotent. Increasing $f$ sharpens each column toward its largest entries and yields more, smaller clusters, so $f$ controls granularity.

Repeating the clustering over $B$ resampled versions of the data gives a consensus matrix $C_{kl} = B^{-1}\sum_{b=1}^{B} \mathbf{1}\{k,l \text{ in the same cluster in replicate } b\} \in [0,1]$. The stability score of vertex $k$ is the average of $C_{kl}$ over the vertices $l$ whose co-membership status with $k$ matches the clustering of the full data, and the granularity $f$ is chosen to maximize a stability-weighted silhouette width over the vertices.

## Depends on

- [Jaccard-similarity network of subtype labels](jaccard-similarity-network-of-subtype-labels.md)

## Remarks

Expansion spreads probability along longer paths and inflation contracts it back onto the strongest paths; alternating the two makes flow accumulate inside regions of high edge weight and drain from the sparse cuts between them, so the limit matrix has a block structure. Neither step requires the number of clusters in advance, which is the reason the method suits a graph whose natural number of groups is the question being asked. Since $f$ is a free parameter, the selection rule must be external: resampling converts cluster assignments into co-membership frequencies, and the weighted silhouette rewards a value of $f$ whose clusters are both well separated and reproducible under resampling, rather than merely numerous.

## Sources

- Guinney J, Dienstmann R, Wang X, et al. The consensus molecular subtypes of colorectal cancer. *Nature Medicine* 21:1350-1356 (2015), Online Methods, "Network clustering" and "Cluster evaluation". DOI <https://doi.org/10.1038/nm.3967>. PMCID PMC4636487.
- Van Dongen S. Graph clustering by flow simulation. PhD thesis, University of Utrecht (2000).
