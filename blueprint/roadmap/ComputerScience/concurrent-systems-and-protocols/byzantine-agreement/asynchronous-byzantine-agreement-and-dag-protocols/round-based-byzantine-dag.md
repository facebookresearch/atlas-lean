# Round-based DAG of reliably broadcast vertices

In DAG-based atomic broadcast with $n = 3f + 1$ processes (DAG-Rider, Algorithms 1–2), round $0$ of every local DAG is a predefined, hard-coded set of $2f + 1$ genesis vertices. Each process proceeds in rounds $r = 1, 2, \dots$; in round $r$ it reliably broadcasts a vertex containing a batch of transactions, strong edges to the at least $2f + 1$ vertices of round $r - 1$ in its local DAG, and weak edges to vertices of rounds below $r - 1$ in its local DAG to which the new vertex would otherwise have no path. Reliable broadcast guarantees that all correct processes deliver the same vertex from a given process and round (or none). Delivery is not insertion: a delivered vertex is placed in a buffer if it has strong edges to at least $2f + 1$ vertices of the preceding round, and it is inserted into the local DAG only once all vertices it has strong or weak edges to are already present. A process completes round $r$, and moves to round $r+1$, once its local DAG contains at least $2f + 1$ vertices of round $r$. Local DAGs of correct processes are eventually consistent: every vertex in one eventually appears, with the same edges and predecessors, in all.

## Depends on

- [Reliable broadcast](../../replication-and-consistency/reliable-broadcast.md)
- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Sources

- I. Keidar, E. Kokoris-Kogias, O. Naor, A. Spiegelman, "All You Need is DAG", PODC 2021, arXiv:2102.08325, Section 4 (Algorithms 1 and 2).
- G. Danezis, L. Kokoris-Kogias, A. Sonnino, A. Spiegelman, "Narwhal and Tusk: A DAG-based Mempool and Efficient BFT Consensus", EuroSys 2022, arXiv:2105.11827.
