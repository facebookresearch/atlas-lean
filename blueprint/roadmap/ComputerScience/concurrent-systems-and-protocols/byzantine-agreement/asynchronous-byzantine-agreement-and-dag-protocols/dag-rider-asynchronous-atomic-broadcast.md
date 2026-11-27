# DAG-Rider: asynchronous Byzantine atomic broadcast with zero extra communication for ordering

Let $n = 3f + 1$. On top of the round-based DAG, the DAG-Rider ordering rule groups rounds into waves of four rounds; at the end of each wave a threshold common coin retrospectively selects a leader vertex of the wave's first round, which is committed if at least $2f + 1$ vertices of the wave's fourth round have strong paths (paths of strong edges only) to it. When a process commits the leader $v$ of wave $w$, it walks back through the waves $w-1, w-2, \dots$ down to the last wave it decided: for each such wave $w'$, if the elected leader $v'$ of $w'$ exists in its DAG and there is a strong path from the current anchor $v$ to $v'$, it orders $v'$ before $v$ and makes $v'$ the new anchor (Algorithm 3, lines 39–43). Arbitrary reachability through weak edges is not used in this test. The ordered leaders are then processed from the earliest, and for each leader the vertices of its causal history (reachable by strong or weak edges) not yet delivered are delivered in a deterministic order. With these thresholds this yields asynchronous Byzantine atomic broadcast with optimal resilience, expected $O(1)$ waves per committed leader, amortized $O(n)$ communication per transaction for large batches, no communication beyond building the DAG, and post-quantum safety.

## Proof sketch

Agreement on the order follows because a leader committed by one correct process has $2f + 1$ fourth-round supporters with strong paths to it, and every vertex of a later round has strong edges to $2f + 1$ vertices of the previous round, so by quorum intersection every later wave's leader has a strong path to it (Lemma 1); hence every correct process either commits it directly or orders it while walking back along the strong-path chain from its own committed leader. The coin is unpredictable, so the adversary cannot prevent the selected leader from having enough support with constant probability per wave; fairness follows from weak edges.

## Depends on

- [Round-based DAG of reliably broadcast vertices](round-based-byzantine-dag.md)
- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [Cardinality conditions for threshold Byzantine quorum systems and masking-register safety](../byzantine-broadcast-and-quorum-systems/cardinality-conditions-for-threshold-byzantine-quorum-systems-and-masking-regist.md)

## Sources

- I. Keidar, E. Kokoris-Kogias, O. Naor, A. Spiegelman, "All You Need is DAG", PODC 2021, arXiv:2102.08325, Algorithms 1–3 and Lemma 1.
