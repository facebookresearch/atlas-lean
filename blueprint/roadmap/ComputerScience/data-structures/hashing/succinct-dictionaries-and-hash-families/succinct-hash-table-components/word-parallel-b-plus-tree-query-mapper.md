# Word-parallel split-only B+-tree query mapper

The *query mapper* of a bucket is a B+-tree of bounded height whose nodes hold fewer than $2t$ fingerprints packed into a single machine word, ranked by word-parallel comparison, so each node is searched in $O(1)$ word operations. Insertion splits every full node on the way down (top-down proactive splitting), so no split ever propagates upward, and deletion is lazy (leaves may become underfull, and the height is bounded in terms of the number of insertions since the mapper was built rather than the current number of keys). Lookup, insertion, update and deletion take $O(\text{height})$ word operations, which is $O(1)$ for fanout $t = \Theta(\sqrt{\log n})$ when at most polylogarithmically many insertions reach the mapper between rebuilds.

Bender, Farach-Colton, J. Kuszmaul and W. Kuszmaul (Lemma 4.2) implement the query mapper as a B-tree with $B = \sqrt{\log n}$ whose nodes, of $O(\sqrt{\log n}\,\log\log n)$ bits, are operated on by exhaustive subtabulation (lookup tables); replacing the tables by word-parallel ranking and using split-only insertion with lazy deletion is a variant that is not in that paper. Top-down splitting of full nodes is the B-tree insertion of Cormen et al. (Section 18.2).

## Depends on

- [B+-tree of minimum degree t](../../../search-trees/b-plus-trees/b-plus-tree.md)
- [Word-parallel rank of packed fingerprints](../succinct-hash-tables/word-parallel-rank-of-packed-fingerprints.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), pp. 363-373, 2024 (Lemma 4.2).
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009 (Chapter 18).
