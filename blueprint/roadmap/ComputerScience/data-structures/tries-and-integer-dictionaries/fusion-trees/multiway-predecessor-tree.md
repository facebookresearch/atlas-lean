# Static multiway predecessor tree with cached minima

A *multiway predecessor tree* with branching parameter $B \ge 2$ stores a sorted list of keys in its leaves; each internal node has between two and $B$ children and caches the minimum key of each child's subtree, and singleton branches are collapsed. A predecessor query at an internal node selects the last child whose cached minimum is at most the query (stopping if there is none) and recurses. Building the tree bottom-up by grouping consecutive blocks of $B$ subtrees gives height at most $\lceil \log_B n \rceil$ on $n$ keys.

## Depends on

- [Static predecessor problem on word keys](static-predecessor-problem.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- D. Comer, "The Ubiquitous B-Tree", ACM Computing Surveys 11(2), 1979.
