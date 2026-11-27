# Minimap of a fixed-capacity leaf

Let $r \ge 1$ be an integer and suppose the word length satisfies $w = \Omega(n' \log_2(U' r) + \log_2 X)$. A *minimap* (Li, Liang, Yu and Zhou, Lemma 3.7) stores exactly $n'$ key-value pairs with distinct keys from a small key universe $[U']$ and payloads in $[X]$, separating metadata from slots, in three steps.

1. Each payload is split by the spillover representation with parameter $r n'$ into a spill value in $[K^*]$, $K^* \le 2 r n'$, and an $M^*$-bit slot word.
2. The sorted keys $x_1 < \dots < x_{n'}$ together with the spill values $k^*_1, \dots, k^*_{n'}$ of their payloads form one element of a set of $\binom{U'}{n'} (K^*)^{n'}$ tuples, which is split by the spillover representation with parameter $r$ into a spill value $k \in [K]$, $K \le 2r$, and a block of memory bits that fits in $O(1)$ words.
3. A run of $n' M^*$ consecutive memory bits forms $n'$ slots of $M^*$ bits, and the slot word of each key is stored in the slot assigned to it by a dynamic matching scheme between the $n'$ keys and the slots $[n']$.

The minimap consists of the memory bits of steps 2 and 3 together with the spill value $k$, which is passed to the enclosing structure. Queries decode the metadata with lookup tables shared by all minimaps with the same parameters $U'$, $X$, $n'$ and $r$, in $O(1)$ time; an update re-encodes the $O(1)$ words of step 2 and relocates the slots whose assignment changes. At the leaves of their dictionary Li, Liang, Yu and Zhou use the minimap with $r = 1$, keys the identifiers and payloads the quotients (Section 5.2).

## Depends on

- [Spillover representation of a bounded integer](../succinct-hash-tables/spillover-representation.md)
- [Memoryless dynamic matching of balls to bins](memoryless-dynamic-matching.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536 (Lemma 3.7 and its proof; Section 5.2).
- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 305-313, 2008.
