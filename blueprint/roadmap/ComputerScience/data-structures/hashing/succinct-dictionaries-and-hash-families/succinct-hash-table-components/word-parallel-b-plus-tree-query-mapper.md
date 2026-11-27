# Word-parallel split-only B+-tree query mapper

The *query mapper* of a bucket is a B+-tree of bounded height whose nodes hold fewer than $2t$ fingerprints packed into a single machine word, ranked by word-parallel comparison, so each node is searched in $O(1)$ word operations. Insertion splits every full node on the way down (top-down proactive splitting), so no split ever propagates upward, and deletion is lazy (leaves may become underfull). Lookup, insertion, update and deletion take $O(\text{height})$ word operations, which is $O(1)$ for buckets of polylogarithmic size and fanout $t = \Theta(\sqrt{\log n})$.

## Depends on

- [B+-tree of minimum degree t](../../../search-trees/b-plus-trees/b-plus-tree.md)
- [Word-parallel rank of packed fingerprints](../succinct-hash-tables/word-parallel-rank-of-packed-fingerprints.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
