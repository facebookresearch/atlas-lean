# A leaf minimap wastes a constant number of bits

Let the minimap of $n'$ keys of $[U']$ with payloads in $[X]$ use redundancy parameter $r = 1$, as at the leaves of Li, Liang, Yu and Zhou (Section 5.2), let its dynamic matching be the multi-round circle matching, and let it be stored in a fixed-length block of whole bits, its spill value written out in $\lceil \log_2 K \rceil$ bits instead of being passed on. Then the block has at most

$$
\log_2\left(\binom{U'}{n'} X^{n'}\right) + O(1)
$$

bits: Lemma 3.7 of the source incurs at most $4/r$ bits of redundancy, and storing the spill value in whole bits adds at most one more. Queries take $O(1)$ time, and an insertion or deletion changes $O(T + 1)$ slots, where $T$ is the number of rounds of the circle matching, and so $O(\log \max(n', 2))$ slots in expectation.

## Proof sketch

In the proof of Lemma 3.7, splitting the $n'$ payloads with parameter $r n'$ costs at most $n' \cdot 2/(r n') = 2/r$ bits, and splitting the metadata tuple with parameter $r$ at most $2/r$ more, by the redundancy bound of the spillover representation; the metadata tuples number $\binom{U'}{n'} (K^*)^{n'}$, so the memory bits and the spill universe together carry at most $\log_2(\binom{U'}{n'} X^{n'}) + 4/r$ bits. Writing the spill value $k \in [K]$ in $\lceil \log_2 K \rceil$ bits adds less than one bit (Section 5.2). Derived from these two bounds, not stated in this form by the source: with $r = 1$ the block has at most $\log_2(\binom{U'}{n'} X^{n'}) + 5$ bits. Slot changes are bounded by the relocations of the matching (Lemma 3.2, Claims 3.3 and 3.4), plus a rewrite of the $O(1)$-word metadata.

## Depends on

- [Minimap of a fixed-capacity leaf](minimap-of-a-leaf.md)
- [Multi-round consistent-hashing matching on a circle](multi-round-circle-matching.md)

## Proof depends on

- [Redundancy of the spillover representation](../succinct-hash-tables/redundancy-of-spillover.md)
- [Rounds and relocations of multi-round circle matching](rounds-and-relocations-of-circle-matching.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536 (Lemma 3.7 and its proof; Section 5.2, leaf nodes).
- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 305-313, 2008.
