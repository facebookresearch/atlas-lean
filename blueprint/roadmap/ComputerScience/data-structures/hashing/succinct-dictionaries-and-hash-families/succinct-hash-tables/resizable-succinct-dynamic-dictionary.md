# Resizable succinct dynamic dictionary

On the resizable Word RAM there is a randomized implementation of the dynamic dictionary over keys $[U]$ (with no fixed capacity) whose resting space after each operation, when $n$ keys are stored, and whose peak space during capacity migrations are both at most $\mathrm{OPT}(U, V, n) + O(n \log \log n)$ bits, and in which every operation takes expected amortized $O(1)$ instructions against operation sequences fixed in advance. Capacity changes are handled by epochs: when the number of keys leaves the current epoch's range, the table is migrated in place to new parameters by streaming its items, so that the old and new representations never coexist beyond the information-theoretic bound.

## Proof sketch

Within an epoch the structure is the fixed-capacity succinct dictionary with compacted metadata. Migration between epochs copies blocks of items along a single tape, shifting and compacting in place, and its cost is charged to the $\Omega(n)$ operations of the epoch.

## Depends on

- [Resizable Word RAM (virtual memory model)](../../../data-structure-interfaces-and-refinement/resizable-word-ram.md)
- [Information-theoretic space bound for dictionaries](../dictionary-specifications/information-theoretic-dictionary-space.md)

## Proof depends on

- [Fixed-capacity succinct dictionary with deletions in expected amortized constant time](fixed-capacity-succinct-dictionary.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- W. Kuszmaul, J. Liang and R. Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", Proceedings of the ACM-SIAM Symposium on Discrete Algorithms (SODA), 2026.
