# Client-preprocessing single-server PIR

In the *client-preprocessing* (subscription) model of single-server PIR, an offline phase lets the client stream the database once and store a small local state of *hints*; afterwards, in the online phase, the client answers each of an arbitrary adaptive sequence of queries $i_1, i_2, \dots$ by sending one message to the server, which answers with work sublinear in $n$, and then refreshes its hints. *Correctness* requires every online query to return the correct entry (with high probability), and *privacy* requires the server's view of all online queries (and of the offline phase) to be independent of the queried indices, for adaptively chosen query sequences. A sufficient criterion: if a projection of the client state onto what influences the next query is invariant in distribution under every query (the state after a query has the same projected law as a fresh state), then every adaptive query transcript is distributed identically for all index sequences.

## Depends on

- [Private information retrieval schemes](../pir-schemes.md)

## Sources

- Mingxun Zhou, Andrew Park, Wenting Zheng and Elaine Shi, "Piano: Extremely Simple, Single-Server PIR with Sublinear Server Computation", 2024 IEEE Symposium on Security and Privacy (SP), 2024.
