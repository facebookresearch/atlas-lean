# Approximate neighbor search by product quantization

Split the embedding into equal-length contiguous coordinate blocks, so the number of blocks divides the embedding dimension. For block $b$ keep a finite nonempty codebook $C_b$ and encode a database vector $y$ by an index $s_b(y)$ of its nearest block centroid (first index on a tie). For a query $x$, asymmetric distance computation ranks those codes by

$$\widehat d^2(x,y)=\sum_b\|x_b-C_b[s_b(y)]\|_2^2.$$

This is exactly the squared distance from the uncompressed query to the reconstructed database vector, not usually to $y$. One distance table per query block suffices: scoring a code sums one lookup per block. Even if every code is scanned, quantization can reverse the true neighbor order. An inverted-file index can additionally skip candidates; it is not required by product quantization.

## Depends on

- [Exact top-k neighbors in embedding space](top-k-neighbors-in-embedding-space.md)

## Background

- [Approximate near-neighbour problem](../../randomized-algorithms/approximate-near-neighbor-search/approximate-near-neighbor-problem.md)

## Sources

- Jégou, Douze and Schmid, [*Product Quantization for Nearest Neighbor Search*](https://doi.org/10.1109/TPAMI.2010.57) (IEEE TPAMI 2011), sections on product quantization and asymmetric distance computation; Johnson, Douze and Jégou, [*Billion-scale similarity search with GPUs*](https://arxiv.org/abs/1702.08734), the sections “Compressed-domain search” and “Product quantizer”.
