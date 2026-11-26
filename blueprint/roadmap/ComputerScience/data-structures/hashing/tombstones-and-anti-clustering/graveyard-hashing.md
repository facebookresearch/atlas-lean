# Graveyard hashing

*Graveyard hashing* is ordered linear probing with tombstones in which, at every rebuild performed when the load factor is $1 - 1/x$, the table additionally plants $\Theta(n/x)$ *primitive tombstones* at evenly spaced hash positions (one per $\Theta(x)$ consecutive hash values), and rebuilds happen every $\Theta(n/x)$ operations. Primitive tombstones behave like ordinary tombstones: queries skip them and insertions may reuse them.

## Depends on

- [Ordered linear probing](ordered-linear-probing.md)

## Sources

- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250.
