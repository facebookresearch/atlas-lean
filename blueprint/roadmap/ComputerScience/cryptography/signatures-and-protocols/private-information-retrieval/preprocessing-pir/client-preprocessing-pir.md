# Client-preprocessing single-server PIR

In the *client-preprocessing* (subscription) model of single-server PIR, an offline phase, run once, lets the client interact with the server holding the database (in Piano, by streaming the database once) and store a small local state of *hints*; afterwards, in the online phase, the client answers each of an arbitrary adaptive sequence of queries $i_1, i_2, \dots$ by sending one message to the server, which answers with one message (with work sublinear in $n$ in Piano), and then updates its hints. *Correctness* requires that for every database and every query sequence an honest execution returns all correct entries with probability at least $1 - \mathrm{negl}$. *Privacy* requires a polynomial-time simulator that is not given the queries such that, for every polynomial-time server that may deviate from the protocol and adaptively chooses each next query, its view with the simulator is computationally indistinguishable from its view with the honest client, over the offline phase and all online queries (Zhou, Park, Zheng and Shi, Section 3.1, Definition 3.1).

## Depends on

- [Private information retrieval schemes](../pir-schemes.md)

## Sources

- Mingxun Zhou, Andrew Park, Wenting Zheng and Elaine Shi, "Piano: Extremely Simple, Single-Server PIR with Sublinear Server Computation", 2024 IEEE Symposium on Security and Privacy (SP), 2024, Section 3.1 and Definition 3.1 (numbered as in the full version, Cryptology ePrint Archive, Paper 2023/452).
