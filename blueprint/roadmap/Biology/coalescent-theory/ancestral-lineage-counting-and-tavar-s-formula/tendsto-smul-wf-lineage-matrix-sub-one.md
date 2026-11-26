# Scaled Wright–Fisher lineage matrix converges to Kingman's generator

For every natural number $n$, the matrices $M\,(P_{n,M} - I)$ converge entrywise to the block-counting generator $G_n$ as the natural number $M$ tends to infinity, where $P_{n,M}$ is the [Wright–Fisher transition matrix of the lineage count](wf-lineage-matrix.md) and $G_n$ the [generator of Kingman's block-counting process](block-counting-generator.md). In words: in one generation, $k$ lineages coalesce to $k - 1$ with probability $\binom{k}{2}/M + o(1/M)$, and to fewer with probability $O(1/M^2)$.
