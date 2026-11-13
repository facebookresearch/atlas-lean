# Scaled Wright–Fisher lineage matrix converges to Kingman's generator

The scaled one-generation increment `M • (wfLineageMatrix n M - 1)` converges entrywise to
the block-counting generator: `k` lineages coalesce to `k - 1` with probability
`(k.choose 2) / M + o(1/M)`, and to fewer with probability `O(1/M²)`.
