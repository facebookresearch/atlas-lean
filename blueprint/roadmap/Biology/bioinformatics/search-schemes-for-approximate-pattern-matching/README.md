# Search schemes for approximate pattern matching

Lossless approximate pattern matching with up to $k$ mismatches or edits in a bidirectional full-text index is organized by search schemes: the pattern is split into parts, and each search processes the parts in a contiguous order with cumulative error bounds that grow slowly, so that the dense region near the root of the search tree is explored with few errors.

- [Search schemes and the pigeonhole principle](search-schemes-and-the-pigeonhole-principle.md)
- [Cluster centres of banded edit-distance matrices](cluster-centres-of-banded-edit-distance-matrices.md)
