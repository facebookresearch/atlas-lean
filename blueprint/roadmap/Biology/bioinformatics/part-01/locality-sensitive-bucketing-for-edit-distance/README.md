# Locality-sensitive bucketing for edit distance

A locality-sensitive bucketing (LSB) function sends each length-$n$ sequence to a set of buckets so that sequences within edit distance $d_1$ always share a bucket and sequences at edit distance at least $d_2$ never do. It generalizes deterministic locality-sensitive hashing by allowing several buckets per sequence, which makes exact (gap-free or small-gap) separation possible for seed-and-compare pipelines on biological sequences.

- [Optimal (1, 2)-sensitive bucketing function](optimal-1-2-sensitive-bucketing-function.md)
- [Guaranteed subsets and gapped bucketing functions](guaranteed-subsets-and-gapped-bucketing-functions.md)
