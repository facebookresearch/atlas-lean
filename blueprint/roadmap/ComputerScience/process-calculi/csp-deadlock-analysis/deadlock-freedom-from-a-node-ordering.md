# Deadlock-freedom from a node ordering

Let $V$ be a [network](networks-of-csp-processes.md) satisfying assumptions (A)–(E) that is free of conflict (see [Ungranted requests and conflicts in CSP networks](ungranted-requests-and-conflicts.md)). A *node ordering* is a partial order $<$ on the processes of $V$ in which any two processes adjacent in the communication graph are comparable. If $V$ has a node ordering such that, in every state, whenever a process $P_i$ makes a request to some neighbour $P_j < P_i$ it makes a request to every neighbour $P_k < P_i$, then $V$ is deadlock-free. Here a request is the ordinary one, not necessarily ungranted: two neighbours that both offer a shared event make requests to each other.

## Depends on

- [Networks of CSP processes and deadlock](networks-of-csp-processes.md)
- [Ungranted requests and conflicts in CSP networks](ungranted-requests-and-conflicts.md)

## Proof depends on

- [The fundamental principle of deadlock](fundamental-principle-of-deadlock.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 13.2.1, the definition of a node ordering, Deadlock rule 2 and its proof, p. 350.
