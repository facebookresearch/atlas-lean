# Exact top-k neighbors in embedding space

Let $e:X\to\mathbb R^d$ be a fixed encoder, $q\in X$ a query, and $x_1,\ldots,x_n$ an indexed database with $1\le k\le n$. Sort the index–score pairs by $(\|e(q)-e(x_i)\|_2^2,i)$ in ascending lexicographic order. The first $k$ distinct indices, in order, are the exact embedding neighbors. Ties are resolved by index; duplicate vectors need not denote duplicate records.

For nonzero embeddings normalized to unit length, $\|u-v\|_2^2=2-2u^\top v$, so the same neighbors result from sorting by decreasing cosine similarity with the same tie convention. Without normalization the rankings can differ.

## Background

- [Nearest Neighbor Index](../pac-learning/1-nearest-neighbor-rule/nearest-neighbor-index.md)

## Sources

- Johnson, Douze and Jégou, [*Billion-scale similarity search with GPUs*](https://arxiv.org/abs/1702.08734), §2, “Problem statement” and “Exact search”; the index tie-break fixes a choice among equal scores.
