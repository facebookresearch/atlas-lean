# PGPS finishes within one packet time of GPS

In a [PGPS](packet-by-packet-generalized-processor-sharing.md) node of total rate $c$ whose packets have size at most $L$, every packet finishes transmission no later than its GPS finish time plus $L/c$.

## Depends on

- [Packet-by-packet generalized processor sharing](packet-by-packet-generalized-processor-sharing.md)

## Expansion

This page becomes ready once its proof is stated and checked: the source quotes the result from Parekh and Gallager (1993) without proof. The proof rests on the lemma that packets arriving later do not change the relative GPS departure order of the packets already present, and uses it to show that a packet sent by PGPS after packets with later GPS finish times is delayed by at most one maximum-size packet.

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 2.1.2, Proposition 2.1.1.
- A. K. Parekh and R. G. Gallager, "A generalized processor sharing approach to flow control in integrated services networks: the single-node case", *IEEE/ACM Transactions on Networking* 1(3):344–357, 1993, the result quoted there.
