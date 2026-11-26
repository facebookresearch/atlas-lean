# A full minimap wastes at most three bits

At full capacity $m = n'$, the minimap representation uses at most $\log_2\left(\binom{U'}{n'} X^{n'}\right) + 3$ bits, its contents are uniquely determined by the represented map (the encoding is canonical and history independent), and an insertion, deletion or replacement changes $O(T)$ slots deterministically and $O(\log \max(n', 2))$ slots in expectation, where $T$ is the number of rounds of the underlying circle matching.

## Proof sketch

The metadata index ranges over $\binom{U'}{n'} K^{n'}$ values and the slots hold $n' M$ bits, so the total is $\lceil \log_2 \binom{U'}{n'} + n' \log_2 K \rceil + n'M$; by the spillover bound $n'(M + \log_2 K - \log_2 X) \le 2$, and the rounding adds less than one bit. Canonicity follows because the matching is memoryless and the metadata is a bijective encoding. Slot changes are bounded by the relocations of the matching.

## Depends on

- [Minimap of a fixed-capacity leaf](minimap-of-a-leaf.md)

## Proof depends on

- [Redundancy of the spillover representation](../succinct-hash-tables/redundancy-of-spillover.md)
- [Rounds and relocations of multi-round circle matching](rounds-and-relocations-of-circle-matching.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
