# Order min hash for edit distance

Locality-sensitive hashing lets one find similar sequences without comparing all pairs, but k-mer set similarities (Jaccard, weighted Jaccard) ignore the order of k-mers and can rate sequences with very different edit distances as identical. Order min hash (OMH) samples several uniquified k-mers by a random permutation and records them in their order of appearance in the sequence, which yields a gapped locality-sensitive hash family for the edit similarity.

- [Order min hash is locality-sensitive for the edit similarity](order-min-hash-is-locality-sensitive-for-the-edit-similarity.md)
