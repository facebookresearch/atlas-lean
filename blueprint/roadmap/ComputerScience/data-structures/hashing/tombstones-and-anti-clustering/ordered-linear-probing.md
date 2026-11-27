# Ordered linear probing

*Ordered linear probing* (Amble and Knuth) maintains the invariant that within every maximal run of non-free slots the stored keys and tombstones (a tombstone carrying the hash of the key whose deletion left it) appear in nondecreasing order of hash value, read along the run in its unrolled order: for a run starting at slot $s$ of a table of $n$ slots, an entry with hash $h$ is compared by its offset $(h - s) \bmod n$, so a run that wraps past the last slot stays sorted (in a table of $8$ slots, hashes $7, 7, 0$ in slots $7, 0, 1$ have offsets $0, 0, 1$). Ties are broken by a fixed order on keys. An insertion of $u$ scans from $h(u)$ to the position where $u$ belongs in this order and shifts the remainder of the run by one slot; with tombstones, a tombstone encountered at or after the insertion point may absorb the shift. Ordered linear probing stores exactly the same set of occupied positions as standard linear probing for any insertion-only sequence, and a query for an absent key can stop as soon as it passes the position its hash order dictates.

## Depends on

- [Linear probing with tombstones and periodic rebuilds](linear-probing-with-tombstones.md)

## Sources

- Ole Amble, Donald E. Knuth, "Ordered Hash Tables", The Computer Journal 17(2) (1974).
- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250.
