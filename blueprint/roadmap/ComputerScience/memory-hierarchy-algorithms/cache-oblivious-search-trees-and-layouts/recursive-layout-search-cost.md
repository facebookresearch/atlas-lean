# Root-to-leaf paths in the recursive layout touch $O(\log_L N)$ lines

For every line length $L \ge 2$, every root-to-leaf path of a complete binary tree on $N$ nodes stored in the van Emde Boas layout touches at most $4\lceil \log_L N\rceil + O(1)$ cache lines; hence a search costs $O(1 + \log_L N)$ cache misses in the ideal-cache model for every $L$ simultaneously. The additive $1$ cannot be dropped: for $L > N$ the first, cold read of the root is already a miss while $\log_L N < 1$.

## Proof sketch

Consider the coarsest level of the recursion at which the subtrees have height $h'$ with $\sqrt{L} \le 2^{h'} \le L$, so each such subtree has fewer than $L$ nodes and is stored contiguously, hence spans at most two lines. A root-to-leaf path crosses at most $\lceil \log_2 N / h' \rceil \le 2\log_L N + 1$ such subtrees, since $h' \ge \frac12 \log_2 L$, giving at most $4\log_L N + O(1)$ lines.

## Depends on

- [Prokop's recursive layout of a complete binary tree](recursive-tree-layout.md)
- [The ideal-cache model](../cache-oblivious-algorithms/the-ideal-cache-model.md)

## Sources

- Harald Prokop, "Cache-Oblivious Algorithms", Master's thesis, Massachusetts Institute of Technology (1999).
- Michael A. Bender, Erik D. Demaine, Martín Farach-Colton, "Cache-Oblivious B-Trees", SIAM Journal on Computing 35(2) (2005); FOCS (2000), Lemma 2.2.
