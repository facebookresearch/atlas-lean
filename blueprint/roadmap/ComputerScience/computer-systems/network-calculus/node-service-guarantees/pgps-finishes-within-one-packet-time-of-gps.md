# PGPS finishes within one packet time of GPS

In a [PGPS](packet-by-packet-generalized-processor-sharing.md) node of total rate $c$ whose packets have size at most $L$, every packet finishes transmission no later than its GPS finish time plus $L/c$.

## Depends on

- [Packet-by-packet generalized processor sharing](packet-by-packet-generalized-processor-sharing.md)

## Expansion

This page becomes ready once a fluid GPS model with per-packet finish times is stated: the [GPS page](../generalized-processor-sharing-offers-a-constant-rate-service-curve.md) defines GPS only by its rate guarantee. The source's proof, after Proposition 2.1.1, then needs that GPS and PGPS, both work conserving at total rate $c$, have the same busy periods. It takes the last packet $m_0$ sent by PGPS before packet $n$ whose GPS finish time is later, and notes that the packets $m_0 + 1, \dots, n$ arrived after $m_0$ started, by the PGPS selection rule. Counting the GPS service between that start and the GPS finish time of $n$ then gives the bound $L/c$.

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 2.1.2, Proposition 2.1.1.
- A. K. Parekh and R. G. Gallager, "A generalized processor sharing approach to flow control in integrated services networks: the single-node case", *IEEE/ACM Transactions on Networking* 1(3):344–357, 1993, the result quoted there.
