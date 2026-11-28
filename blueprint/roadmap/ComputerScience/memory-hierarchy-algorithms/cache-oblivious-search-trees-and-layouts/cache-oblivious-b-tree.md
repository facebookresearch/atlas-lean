# Cache-oblivious B-trees

There is a cache-oblivious dynamic search tree on $N$ keys that supports searches in $O(1 + \log_{L+1} N)$ cache misses and insertions and deletions in $O\!\left(1 + \log_{L+1} N + \frac{\log^2 N}{L}\right)$ amortized cache misses, for every line length $L$ simultaneously, and scans of $K$ consecutive keys in $O(1 + K/L)$ misses after the search, so range queries cost $O(1 + \log_{L+1} N + K/L)$. This matches the search bound of B-trees without knowing $L$, and their update bound when $L = \Omega(\log N\log\log N)$. Without the scan operation, a variant supports updates in $O(1 + \log_{L+1} N)$ amortized cache misses.

## Proof sketch

Store a strongly weight-balanced search tree in the van Emde Boas layout inside a packed memory array, so searches cost $O(1+\log_{L+1} N)$ by the recursive-layout lemma. Splitting or merging a node of height $h$ moves its recursive subtrees by a constant number of scans, $O(1 + d^h/L)$ misses for branching parameter $d$, which weight balance amortizes to $O(1 + \log_{L} N)$ per update. Updating pointers to the $O(\log^2 N)$ amortized elements a packed-memory rebalance moves could cost $O(\log^2 N)$ misses, so two layers of indirection group the elements into blocks of $\Theta(\log N)$ and keep only representatives in the tree, leaving the $O(\log^2 N / L)$ term of the packed memory array at the bottom layer.

## Depends on

- [The ideal-cache model](../cache-oblivious-algorithms/the-ideal-cache-model.md)

## Proof depends on

- [Root-to-leaf paths in the recursive layout touch $O(1 + \log_L N)$ lines](recursive-layout-search-cost.md)
- [Amortized cost of packed memory arrays](packed-memory-array-cost.md)
- [Packed memory arrays](packed-memory-array.md)
- [Prokop's recursive layout of a complete binary tree](recursive-tree-layout.md)

## Sources

- Michael A. Bender, Erik D. Demaine, Martín Farach-Colton, "Cache-Oblivious B-Trees", SIAM Journal on Computing 35(2) (2005); FOCS (2000).
