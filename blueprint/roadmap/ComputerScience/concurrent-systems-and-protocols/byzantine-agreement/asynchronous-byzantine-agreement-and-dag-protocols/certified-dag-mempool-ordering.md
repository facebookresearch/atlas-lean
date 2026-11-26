# Separating data dissemination from ordering: certified DAG mempools

In a certified DAG mempool with $n \ge 3f + 1$ processes, each vertex of round $r$ becomes certified once $2f + 1$ processes acknowledge storing it, and the certificate (not the data) is referenced by round-$(r+1)$ vertices. Then every certified vertex is available: its data is stored by at least $f + 1$ correct processes and can always be retrieved; the DAG makes progress at network speed whenever $2f + 1$ correct processes are active; and any consensus protocol that orders vertex certificates, in particular a zero-message ordering rule interpreting the DAG with a common coin, yields Byzantine atomic broadcast whose throughput is determined by data dissemination, with an expected constant number of rounds to commit a vertex in the asynchronous case.

## Proof sketch

Availability is quorum intersection: a certificate carries $2f + 1$ storage acknowledgements, at least $f + 1$ from correct processes. Since vertices reference certified predecessors, the causal history of any vertex is available, and ordering only certificates decouples ordering cost from batch size. The asynchronous ordering rule commits a randomly elected leader of every other round when $f + 1$ vertices of the next round reference it, which by an unpredictability argument happens with constant probability per wave.

## Depends on

- [Round-based DAG of reliably broadcast vertices](round-based-byzantine-dag.md)

## Proof depends on

- [Quorums of size n - f intersect in a correct replica when n is at least 3f + 1](../linear-view-change-bft-state-machine-replication/byzantine-quorum-intersection.md)
- [DAG-Rider: asynchronous Byzantine atomic broadcast with zero extra communication for ordering](dag-rider-asynchronous-atomic-broadcast.md)

## Sources

- G. Danezis, L. Kokoris-Kogias, A. Sonnino, A. Spiegelman, "Narwhal and Tusk: A DAG-based Mempool and Efficient BFT Consensus", EuroSys 2022, arXiv:2105.11827.
