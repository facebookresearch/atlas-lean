# Graveyard hashing

*Graveyard hashing* is ordered linear probing with tombstones whose rebuilds depend on the load factor. A rebuild performed at load factor $1 - 1/x$ first removes all tombstones and then plants $n/(2x)$ new tombstones, not created by deletions, one assigned to each of the hashes $2ix$ for $i \in [n/(2x)]$; the next rebuild happens $n/(4x)$ operations later, counting both insertions and deletions. Insertions, deletions and queries are exactly those of ordered linear probing, so the planted tombstones behave like ordinary ones: queries skip them and insertions may reuse them. Optionally each rebuild also resizes the table to keep the load factor at $1 - \Theta(1/x)$ for a fixed $x$.

## Depends on

- [Ordered linear probing](ordered-linear-probing.md)

## Sources

- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250.
