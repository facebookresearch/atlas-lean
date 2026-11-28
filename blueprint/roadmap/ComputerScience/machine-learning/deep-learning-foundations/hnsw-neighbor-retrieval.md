# Querying a hierarchical navigable small-world index

An HNSW index supplies nested proximity graphs on database IDs: level zero contains all IDs and each higher level contains a subset of the preceding level. For a query, start at the designated entry point on the highest level. On each upper level, run a one-candidate search, following improving neighbors until there is no closer neighbor to expand, and descend from the best ID found.

On level zero use a search width $e_f\ge k$ rather than one. Keep a queue of discovered, unexpanded candidates ordered by distance and a bounded collection of the best $e_f$ discovered IDs. Expand the nearest candidate, adding unseen neighbors competitive with the retained set; stop once the queue is empty or the nearest candidate is farther than the worst retained ID in a full set. Return the best $k$ retained IDs when at least $k$ were discovered (otherwise all of them). Use database index to resolve equal-distance choices. The width bounds the retained set, **not** the number of distance evaluations; it is not a worst-case approximation factor.

## Depends on

- [Exact top-k neighbors in embedding space](top-k-neighbors-in-embedding-space.md)

## Background

- [Recall at k for approximate neighbor search](recall-at-k-for-approximate-search.md)
- [Locality-sensitive hashing index with L tables and a stopping rule](../../randomized-algorithms/approximate-near-neighbor-search/lsh-index.md)

## Sources

- Malkov and Yashunin, [*Efficient and robust approximate nearest neighbor search using Hierarchical Navigable Small World graphs*](https://arxiv.org/abs/1603.09320), algorithms 2 and 5 (search on one layer and $k$-NN query).
