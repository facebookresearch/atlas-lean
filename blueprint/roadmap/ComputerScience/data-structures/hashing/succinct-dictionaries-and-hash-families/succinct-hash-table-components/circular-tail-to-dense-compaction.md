# Circular tail-to-dense compaction for resizable succinct tables

In the resizable succinct dictionary, the slots of full slabs map directly to dense indices $[0, F)$, and the active tail slots map bijectively onto a circular window $[b, b + n_w)$ of dense indices modulo the tail capacity. Growing or shrinking the window by one position at either end changes $O(1)$ entries of the tail-to-dense correspondence, and from a dense index the owning bucket and logical slot are recovered in $O(1)$ time. Hence items can be streamed between epochs of different capacity in place, with resting and peak space at most $\mathrm{OPT}(U, V, n) + O(n \log \log n)$ bits.

## Proof sketch

The window is an interval of residues, so moving its endpoints touches only the boundary entries. Bucket ownership is recovered from the prefix structure of the slab counts and the circular offset.

## Depends on

- [Resizable Word RAM (virtual memory model)](../../../data-structure-interfaces-and-refinement/resizable-word-ram.md)
- [Slab storage with hysteresis has amortized constant reorganization cost](slab-storage-with-hysteresis.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- W. Kuszmaul, J. Liang and R. Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", Proceedings of the ACM-SIAM Symposium on Discrete Algorithms (SODA), 2026.
