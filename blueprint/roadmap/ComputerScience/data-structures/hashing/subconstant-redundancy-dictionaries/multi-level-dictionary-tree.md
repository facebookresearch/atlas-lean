# Multi-level dictionary tree with subconstant wasted bits

The *multi-level dictionary tree* for $n$ keys of a universe $n^{1+\alpha_{\min}} \le U \le n^{1+\alpha_{\max}}$ and redundancy parameter $R$ is a tree of bounded depth whose nodes at level $\ell$ hold about $n_\ell$ keys, with $n_0 = n$ at the root and a fixed parameter schedule decreasing $n_\ell$ down to leaf capacity. At each internal node a regime-switched hash family (one-round Feistel permutations with round functions from double tabulation, or from simpler hashing at small nodes) routes each key to a child and compresses its identifier; children have slightly more capacity than their expected load. Leaves are fixed-capacity minimaps. A small waiting list per node absorbs keys arriving while a child is being rebuilt, and subtrees are rebuilt locally when their load leaves the allowed range.

## Depends on

- [Minimap of a fixed-capacity leaf](minimap-of-a-leaf.md)
- [One-round Feistel permutations on mixed domains](one-round-feistel-on-mixed-domains.md)
- [Double tabulation hashing](../word-ram-hash-families/double-tabulation-hashing.md)
- [Information-theoretic space bound for dictionaries](../dictionary-specifications/information-theoretic-dictionary-space.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
