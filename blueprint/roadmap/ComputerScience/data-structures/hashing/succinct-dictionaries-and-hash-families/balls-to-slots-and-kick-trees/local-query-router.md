# Local query router by binary prefix trie

A *local query router* for a group of at most $B$ keys is a binary prefix trie over their fingerprints, stored succinctly (for instance as a bit sequence with rank and select), which maps a query fingerprint to the position of the unique stored key with that fingerprint, or reports absence. It uses $O(B)$ bits beyond the fingerprints and answers in $O(1)$ time by table lookup when $B$ is small.

## Depends on

- [Rank and select on small bit vectors by table lookup](rank-and-select-by-table-lookup.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
