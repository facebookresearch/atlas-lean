# Bit-packed slot tables for kick-tree dictionaries

In the source's fixed-capacity dictionary, a cubby of capacity $K$ stores a storage array of $K$ slots holding the stored key bits (after quotienting, only the bits not recoverable from the position) and the value of each present key; a mini-array of local query routers; a mini-array $M$ recording, for each depth-1 bin, which slots are free and the depth of the key in each occupied slot; after quotienting, a mini-array $B$ recovering the remaining key bits; and a free-slot tree of constant depth and fanout $\log n$ that finds a free slot in $O(1)$ time. Occupancy is therefore read from metadata, never from the stored bits, so a stored all-zero key part or value is distinguished from an empty slot, and every slot read or write takes $O(1)$ time. The fixed-width per-slot fields (stored key part, value, a one-bit occupancy flag and the depth of the occupant) can equally be kept in parallel bit-packed arrays, which also take $O(1)$ word-RAM instructions per slot access and represent the empty cubby by zeroed memory; this flat layout is a word-RAM realization of the cubby slot state, not the source's mini-array encoding.

## Depends on

- [k-kick tree balls-to-slots scheme](k-kick-tree.md)
- [Bit-packed array on the Word RAM](../word-ram-hash-families/bit-packed-array.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602 (Sections 5.1 and 5.3).
