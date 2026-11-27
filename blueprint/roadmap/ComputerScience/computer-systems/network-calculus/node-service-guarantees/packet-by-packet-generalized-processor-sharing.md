# Packet-by-packet generalized processor sharing

A [generalized processor sharing](../generalized-processor-sharing-offers-a-constant-rate-service-curve.md) (GPS) node serves flows as a fluid. *Packet-by-packet generalized processor sharing* (PGPS), also called weighted fair queuing, emulates it with whole packets: it keeps one FIFO queue per flow and transmits one packet at a time, entirely, at the system rate $c$. For every packet it computes its *GPS finish time*, the time at which the packet would complete under GPS with the same weights and the same arrivals; whenever a packet finishes transmission, it selects among the packets present the one with the earliest GPS finish time. PGPS is work conserving, but may send a packet before its GPS finish time.

## Depends on

- [Generalized processor sharing offers a constant-rate service curve](../generalized-processor-sharing-offers-a-constant-rate-service-curve.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 2.1.2 (the description of PGPS and Figure 2.1).
- A. K. Parekh and R. G. Gallager, "A generalized processor sharing approach to flow control in integrated services networks: the single-node case", *IEEE/ACM Transactions on Networking* 1(3):344–357, 1993, cited there for PGPS.
