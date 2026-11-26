# Client-preprocessing single-server PIR

In the *client-preprocessing* (subscription) model of single-server PIR, an offline phase lets the client stream the database once and store a small local state of *hints*; afterwards, in the online phase, the client answers each of an arbitrary adaptive sequence of queries $i_1, i_2, \dots$ by sending one message to the server, which answers with work sublinear in $n$, and then refreshes its hints. *Correctness* requires every online query to return the correct entry (with high probability), and *privacy* requires the server's view of all online queries (and of the offline phase) to be independent of the queried indices, for adaptively chosen query sequences. A sufficient criterion: let $\pi$ be a projection of the client state such that the message for the next query depends only on $\pi(\mathrm{st})$, the queried index and fresh coins; if, whenever $\pi(\mathrm{st})$ has the law of a fresh state, the joint law of the message and the next projected state is the same for every queried index, and the next projected state again has the fresh law independently of the message, then every adaptive query transcript is distributed identically for all index sequences.

## Depends on

- [Private information retrieval schemes](../pir-schemes.md)

## Sources

- Mingxun Zhou, Andrew Park, Wenting Zheng and Elaine Shi, "Piano: Extremely Simple, Single-Server PIR with Sublinear Server Computation", 2024 IEEE Symposium on Security and Privacy (SP), 2024.
