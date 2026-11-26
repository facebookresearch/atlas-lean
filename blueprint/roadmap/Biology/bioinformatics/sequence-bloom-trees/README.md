# Sequence Bloom trees

A sequence Bloom tree indexes many sequencing experiments by a binary tree of Bloom filters: each leaf stores the $k$-mers of one experiment and each internal node stores the union of the $k$-mers below it. A query string is pushed down only through nodes containing at least a fraction $\theta$ of its $k$-mers. The analysis sizes the union filters and bounds the probability that filter false positives make a node falsely report a query.

- [Union Bloom filter size and optimal hash count](union-bloom-filter-size-and-optimal-hash-count.md)
- [Query false-positive bound for sequence Bloom trees](query-false-positive-bound-for-sequence-bloom-trees.md)
