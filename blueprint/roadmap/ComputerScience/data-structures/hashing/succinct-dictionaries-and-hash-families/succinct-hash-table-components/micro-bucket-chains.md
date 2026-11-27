# Micro-bucket chains with two-phase search

In the fixed-capacity succinct dictionary each (bucket, micro-bucket) pair owns a doubly linked chain of the slots in its bucket holding keys with that micro-bucket address, with links of $O(\log \log n)$ bits stored as local slot indices. A search for key $u$ first walks the chain of $u$'s micro-bucket comparing stored quotients (phase 1), and only if this fails consults the bucket's overflow structure (phase 2). Deletion unlinks the found slot and moves the bucket's last item into it, so a bucket's items always occupy a prefix of its local slots.

## Depends on

- [Bucket and micro-bucket address decomposition](bucket-and-micro-bucket-decomposition.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6), 2023.
