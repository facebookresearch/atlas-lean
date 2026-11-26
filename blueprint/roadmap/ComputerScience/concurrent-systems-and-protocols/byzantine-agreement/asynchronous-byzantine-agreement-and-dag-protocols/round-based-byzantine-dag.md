# Round-based DAG of reliably broadcast vertices

In DAG-based atomic broadcast with $n \ge 3f + 1$ processes, each process proceeds in rounds $r = 1, 2, \dots$; in round $r$ it reliably broadcasts a vertex containing a batch of transactions and references (strong edges) to at least $n - f$ vertices of round $r - 1$ that it has delivered, and up to $f$ weak edges to vertices of rounds below $r - 1$ in its local DAG to which the new vertex would otherwise have no path. Reliable broadcast guarantees that all correct processes deliver the same vertex from a given process and round (or none). The local DAG of a correct process consists of all delivered vertices and their edges; local DAGs of correct processes are eventually consistent: every vertex in one eventually appears with the same edges in all.

## Depends on

- [Reliable broadcast](../../replication-and-consistency/reliable-broadcast.md)
- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Sources

- I. Keidar, E. Kokoris-Kogias, O. Naor, A. Spiegelman, "All You Need is DAG", PODC 2021, arXiv:2102.08325.
- G. Danezis, L. Kokoris-Kogias, A. Sonnino, A. Spiegelman, "Narwhal and Tusk: A DAG-based Mempool and Efficient BFT Consensus", EuroSys 2022, arXiv:2105.11827.
