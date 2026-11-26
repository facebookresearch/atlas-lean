# Bullshark: a DAG protocol with a partially synchronous fast path

Bullshark refines the DAG ordering rule so that each wave has two rounds and predefined leader vertices are committed during synchronous periods when at least $f + 1$ vertices of the next round reference them, while retaining the coin-based asynchronous fallback. It preserves the properties of DAG-Rider (asynchronous liveness, optimal amortized communication, fairness, and safety without signatures in the ordering layer) and, after GST in a partially synchronous network, commits a leader every two rounds without any view-change or view-synchronization mechanism. A standalone partially synchronous version uses timeouts in place of the common coin.

## Proof sketch

In synchronous periods, $f + 1$ references to a leader from the next round guarantee by quorum intersection that every correct process's later leader has a path to it, which suffices for consistent ordering in place of the $2f + 1$ threshold used for asynchronous waves. Correct processes vote on which mode applies to each wave through their DAG edges, so the decision to use the fast or fallback leader is itself consistent and requires no extra messages.

## Depends on

- [Round-based DAG of reliably broadcast vertices](round-based-byzantine-dag.md)
- [Partial synchrony](../../distributed-execution-models/partial-synchrony.md)
- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [DAG-Rider: asynchronous Byzantine atomic broadcast with zero extra communication for ordering](dag-rider-asynchronous-atomic-broadcast.md)
- [Quorums of size n - f intersect in a correct replica when n is at least 3f + 1](../linear-view-change-bft-state-machine-replication/byzantine-quorum-intersection.md)

## Sources

- A. Spiegelman, N. Giridharan, A. Sonnino, L. Kokoris-Kogias, "Bullshark: DAG BFT Protocols Made Practical", ACM CCS 2022, arXiv:2201.05677.
- G. Danezis, L. Kokoris-Kogias, A. Sonnino, A. Spiegelman, "Narwhal and Tusk: A DAG-based Mempool and Efficient BFT Consensus", EuroSys 2022, arXiv:2105.11827.
