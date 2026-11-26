# DAG-Rider: asynchronous Byzantine atomic broadcast with zero extra communication for ordering

On top of the round-based DAG, the DAG-Rider ordering rule groups rounds into waves of four rounds; at the end of each wave a threshold common coin retrospectively selects a leader vertex of the wave's first round, which is committed if at least $2f + 1$ vertices of the wave's fourth round have strong paths to it; committed leaders, together with earlier uncommitted leaders reachable from them, are ordered, and each leader's causal history is delivered in a deterministic order. With $n \ge 3f + 1$ this yields asynchronous Byzantine atomic broadcast with optimal resilience, expected $O(1)$ waves per committed leader, amortized $O(n)$ communication per transaction for large batches, no communication beyond building the DAG, and post-quantum safety.

## Proof sketch

Agreement on the order follows because a leader committed by one correct process has $2f + 1$ fourth-round supporters, and by quorum intersection every correct process's later committed leader has a path to it, so every correct process either commits it directly or orders it while traversing back from its own committed leader. The coin is unpredictable, so the adversary cannot prevent the selected leader from having enough support with constant probability per wave; fairness follows from weak edges.

## Depends on

- [Round-based DAG of reliably broadcast vertices](round-based-byzantine-dag.md)
- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [Quorums of size n - f intersect in a correct replica when n is at least 3f + 1](../linear-view-change-bft-state-machine-replication/byzantine-quorum-intersection.md)

## Sources

- I. Keidar, E. Kokoris-Kogias, O. Naor, A. Spiegelman, "All You Need is DAG", PODC 2021, arXiv:2102.08325.
