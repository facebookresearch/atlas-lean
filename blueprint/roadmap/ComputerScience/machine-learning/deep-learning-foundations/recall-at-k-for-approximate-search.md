# Recall at k for approximate neighbor search

Use the exact top-$k$ IDs $T_k(q)$ as the relevant set for query $q$, with $1\le k\le n$ and a fixed index tie rule on the $n$ database records. Let $A_k(q)$ contain **at most** $k$ distinct IDs returned on that database. Mean recall at the cutoff on a nonempty finite set $Q$ of queries is

$$\frac1{|Q|}\sum_{q\in Q}\frac{|A_k(q)\cap T_k(q)|}{k}.$$

Missing positions count as misses: returning only two of the three true neighbors gives $2/3$, not one. This is ordinary recall with relevance supplied by exact embedding search. It measures the whole returned set, not just whether it contains the true first neighbor. It is not a multiplicative distance guarantee.

## Depends on

- [Recall at a cutoff](../../not-yet-classified/recall-at/recall-at.md)
- [Exact top-k neighbors in embedding space](top-k-neighbors-in-embedding-space.md)

## Background

- [Approximate near-neighbour problem](../../randomized-algorithms/approximate-near-neighbor-search/approximate-near-neighbor-problem.md)
- [Locality-sensitive hashing index with L tables and a stopping rule](../../randomized-algorithms/approximate-near-neighbor-search/lsh-index.md)

## Sources

- Aumüller, Bernhardsson and Faithfull, [*ANN-Benchmarks: A Benchmarking Tool for Approximate Nearest Neighbor Algorithms*](https://arxiv.org/abs/1807.05614), §2.1. Their distance-threshold recall admits all records tied at the cutoff; the fixed-ID version here agrees when there is no tie across the cutoff.
