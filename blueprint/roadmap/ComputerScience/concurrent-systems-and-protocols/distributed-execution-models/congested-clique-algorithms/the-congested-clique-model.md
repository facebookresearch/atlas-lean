# The congested clique model

The congested clique has $n$ processors with distinct identifiers $1, \dots, n$, connected by a complete communication network. Computation proceeds in synchronous rounds; in each round every processor may send a possibly different message of $O(\log n)$ bits to each other processor. For graph problems on an $n$-vertex input graph $G$, processor $v$ initially knows the edges incident to vertex $v$ (and their weights), and must output its part of the solution. The model equals CONGEST on the complete graph, with the input graph decoupled from the communication graph; the total bandwidth per round is $\Theta(n^2 \log n)$ bits.

## Depends on

- [The CONGEST model of distributed computing](../../local-distributed-algorithms/deterministic-network-decomposition/the-congest-model.md)

## Sources

- Z. Lotker, B. Patt-Shamir, E. Pavlov, D. Peleg, "Minimum-Weight Spanning Tree Construction in O(log log n) Communication Rounds", SIAM Journal on Computing 35(1) (2005); SPAA 2003.
- C. Lenzen, "Optimal Deterministic Routing and Sorting on the Congested Clique", PODC 2013, arXiv:1207.1852.
