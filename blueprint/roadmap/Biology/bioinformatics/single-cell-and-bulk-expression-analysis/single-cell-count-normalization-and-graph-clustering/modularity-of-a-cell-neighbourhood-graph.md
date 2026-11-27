# Modularity of a partition of a nearest-neighbour cell graph

Let cells be embedded as points $v_1, \dots, v_n$ in a reduced expression space (typically the leading principal components of the [normalized and log-transformed](size-factor-scaling-and-log-transform.md) matrix) and fix $K \in \mathbb{N}$. The $K$-nearest-neighbour graph $G$ has vertex set $\{1, \dots, n\}$ and an edge between $i$ and $i'$ whenever one of the two is among the $K$ nearest of the other in the chosen metric; let $A = (A_{ii'})$ be its adjacency matrix with weights $A_{ii'} \ge 0$, $k_i = \sum_{i'} A_{ii'}$ the degree of $i$ and $2m = \sum_{i, i'} A_{ii'}$.

**Definition (modularity with resolution).** For a partition of the cells into clusters, with $c_i$ the cluster of cell $i$, and a resolution parameter $\gamma > 0$,

$$Q_\gamma \;=\; \frac{1}{2m} \sum_{i, i'} \left( A_{ii'} - \gamma \frac{k_i k_{i'}}{2m} \right) \delta(c_i, c_{i'}),$$

where $\delta$ is the Kronecker delta. At $\gamma = 1$ this is the Newman–Girvan modularity, and a larger $\gamma$ penalizes within-cluster edges more heavily, favouring finer partitions.

**Clustering heuristic.** Modularity-based clustering seeks a partition with large $Q_\gamma$. Exact maximization is NP-hard in general, and the Louvain method used in practice is a greedy multilevel heuristic: it moves single cells, then aggregated clusters, between clusters while $Q_\gamma$ increases, and returns a partition that no such move improves. That partition need not maximize $Q_\gamma$ globally.

**Properties.** $Q_\gamma$ compares the observed within-cluster edge weight with its expectation $\gamma k_i k_{i'} / 2m$ under the configuration null model, which preserves the degree sequence; the partition into one cluster gives $Q_\gamma = 1 - \gamma$ and the partition into singletons gives $Q_\gamma = \frac{1}{2m}\sum_i (A_{ii} - \gamma k_i^2 / 2m)$. These values do not decide between the extremes in general: for the graph with two vertices and one edge, at $\gamma = 1$, the single cluster has $Q_1 = 0$ and the singletons have $Q_1 = -\tfrac12$. A cluster may be refined by rerunning the heuristic on the induced subgraph.

## Depends on

- [Size-factor scaling and the log(x+1) transform of single-cell counts](size-factor-scaling-and-log-transform.md)

## Remarks

The neighbourhood graph is a sparse summary of the geometry of expression space: dense regions become densely connected subgraphs, and only pairs that are already neighbours can be judged, which is what makes community detection cheaper than clustering a full distance matrix. The resolution parameter is essential rather than cosmetic, because plain modularity has a resolution limit: in a graph with $2m$ edges, communities joined by few edges and of total degree below roughly $\sqrt{2m}$ are merged by any maximizer at $\gamma = 1$, so the scale of the partition must be set deliberately and, in practice, chosen by inspecting several resolutions. Two further design choices change the answer: the metric used to build the graph, where correlation-based distances often behave better on expression profiles than Euclidean ones, and $K$ itself, since larger $K$ smooths the graph and suppresses small populations. Subclustering a single cluster can expose genuine cell states, but the optimization returns a partition for any graph, including one built from noise.

## Sources

- M. D. Luecken and F. J. Theis, "Current best practices in single-cell RNA-seq analysis: a tutorial", Molecular Systems Biology 15 (2019), e8746, "Clustering" section, <https://doi.org/10.15252/msb.20188746>, PMCID: PMC6582955.
- M. E. J. Newman and M. Girvan, "Finding and evaluating community structure in networks", Physical Review E 69 (2004), 026113.
- J. Reichardt and S. Bornholdt, "Statistical mechanics of community detection", Physical Review E 74 (2006), 016110.
- V. D. Blondel, J.-L. Guillaume, R. Lambiotte and E. Lefebvre, "Fast unfolding of communities in large networks", Journal of Statistical Mechanics (2008), <https://arxiv.org/abs/0803.0476>.
