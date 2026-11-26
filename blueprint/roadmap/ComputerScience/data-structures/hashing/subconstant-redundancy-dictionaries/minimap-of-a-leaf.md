# Minimap of a fixed-capacity leaf

A *minimap* stores a map from $m \le n'$ active keys of a small key universe $[U']$ to payloads in $[X]$ by separating metadata from slots. Each payload is split by the spillover representation with parameter $r = n'$ into a spill value in $[K]$ and an $M$-bit slot word. The active key set together with the list of spill values (in increasing key order) is encoded as a single metadata index in $\left[\binom{U'}{m} K^m\right]$, and each key's slot word is stored at the bin assigned to it by a dynamic matching scheme. Queries decode the metadata with shared lookup tables.

## Depends on

- [Spillover representation of a bounded integer](../succinct-hash-tables/spillover-representation.md)
- [Memoryless dynamic matching of balls to bins](memoryless-dynamic-matching.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
