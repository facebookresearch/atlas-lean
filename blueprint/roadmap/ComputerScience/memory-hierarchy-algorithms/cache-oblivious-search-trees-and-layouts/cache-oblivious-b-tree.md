# Cache-oblivious B-trees

There is a cache-oblivious dynamic search tree on $N$ keys that supports searches in $O(\log_L N)$ cache misses and insertions and deletions in $O\!\left(\log_L N + \frac{\log^2 N}{L}\right)$ amortized cache misses, for every line length $L$ simultaneously, and range queries reporting $K$ keys in $O(\log_L N + K/L)$ misses. This matches the search bound of B-trees without knowing $L$.

## Proof sketch

Store the keys in a packed memory array and build over its segments a static complete binary search tree in the van Emde Boas layout whose leaves point to the segments. Searches use the recursive-layout lemma; an update modifies the packed memory array and then recomputes the tree nodes above the redistributed window in a postorder that touches the window's ancestors in $O(\log_L N + |W|/L)$ misses, which amortizes via the packed-memory-array analysis. Global rebuilding handles changes of $N$.

## Depends on

- [Root-to-leaf paths in the recursive layout touch $O(\log_L N)$ lines](recursive-layout-search-cost.md)
- [Amortized cost of packed memory arrays](packed-memory-array-cost.md)
- [Comparison-based search needs $\Omega(\log_B N)$ I/Os](external-search-lower-bound.md)
- [Raw B-trees](../../data-structures/search-trees/b-tree/btree.md)

## Proof depends on

- [Root-to-leaf paths in the recursive layout touch $O(\log_L N)$ lines](recursive-layout-search-cost.md)
- [Amortized cost of packed memory arrays](packed-memory-array-cost.md)
- [Comparison-based search needs $\Omega(\log_B N)$ I/Os](external-search-lower-bound.md)
- [Raw B-trees](../../data-structures/search-trees/b-tree/btree.md)

## Sources

- Michael A. Bender, Erik D. Demaine, Martín Farach-Colton, "Cache-Oblivious B-Trees", SIAM Journal on Computing 35(2) (2005); FOCS (2000).
