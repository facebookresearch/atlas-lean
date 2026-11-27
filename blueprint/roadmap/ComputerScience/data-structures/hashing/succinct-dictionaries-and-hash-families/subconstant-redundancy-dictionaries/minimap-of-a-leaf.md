# Minimap of a fixed-capacity leaf

A *minimap* stores a map from $m \le n'$ active keys of a small key universe $[U']$ to payloads in $[X]$ by separating metadata from slots. Each payload is split by the spillover representation with parameter $r = n'$ into a spill value in $[K]$, $K \le 2n'$, and an $M$-bit slot word. The number $m$ of active keys, the active key set and the list of spill values (in increasing key order) are encoded together as a single metadata index in $\left[\sum_{j=0}^{n'} \binom{U'}{j} K^j\right]$, the indices for $m$ active keys forming the block of $\binom{U'}{m} K^m$ consecutive values after the blocks for $j < m$, so the index determines $m$ and decoding needs no separate count; and each key's slot word is stored at the bin assigned to it by a dynamic matching scheme. With $n' \le U'$, the word size satisfies $w = \Omega(n' \log_2 U' + \log_2 X)$, so the metadata, of $O(\log_2(n' + 1) + n' \log_2 (U' K)) = O(n' \log_2 U')$ bits, fits in $O(1)$ words; queries decode it with lookup tables shared by all minimaps with the same parameters, in $O(1)$ time, and an update rewrites the metadata and relocates the slots whose bins change. This is the minimap of Li, Liang, Yu and Zhou (Lemma 3.7, as used with redundancy parameter $1$ at the leaves in Section 5.2), except that their minimap applies the spillover representation a second time to the metadata, while here the metadata index is stored in whole bits.

## Depends on

- [Spillover representation of a bounded integer](../succinct-hash-tables/spillover-representation.md)
- [Memoryless dynamic matching of balls to bins](memoryless-dynamic-matching.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 305-313, 2008.
