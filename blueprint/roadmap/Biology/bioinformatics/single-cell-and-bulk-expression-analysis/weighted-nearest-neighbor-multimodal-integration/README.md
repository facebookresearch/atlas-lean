# Weighted nearest neighbor multimodal integration

When several molecular modalities (RNA, surface protein, chromatin accessibility) are measured in the same single cells, each cell can be assigned a vector of modality weights that measures how well each modality's own neighbourhood predicts that cell's profile. A weighted combination of per-modality affinities then defines a single nearest-neighbour graph, and that graph can supervise a linear dimensional reduction of one modality.

- [Cell-specific modality weights and the weighted nearest neighbor graph](cell-specific-modality-weights-and-the-wnn-graph.md)
- [Supervised principal component analysis by HSIC maximization](supervised-pca-by-hsic-maximization.md)
