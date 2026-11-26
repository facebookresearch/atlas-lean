# Ordered linear probing

*Ordered linear probing* (Amble and Knuth) maintains the invariant that within every maximal run of non-free slots the stored keys appear in nondecreasing order of hash value (with a fixed tie-break by key). An insertion of $u$ scans from $h(u)$ to the position where $u$ belongs in this order and shifts the remainder of the run by one slot; with tombstones, a tombstone encountered at or after the insertion point may absorb the shift. Ordered linear probing stores exactly the same set of occupied positions as standard linear probing for any insertion-only sequence, and a query for an absent key can stop as soon as it passes the position its hash order dictates.

## Depends on

- [Linear probing with tombstones and periodic rebuilds](linear-probing-with-tombstones.md)

## Sources

- Ole Amble, Donald E. Knuth, "Ordered Hash Tables", The Computer Journal 17(2) (1974).
- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250.
