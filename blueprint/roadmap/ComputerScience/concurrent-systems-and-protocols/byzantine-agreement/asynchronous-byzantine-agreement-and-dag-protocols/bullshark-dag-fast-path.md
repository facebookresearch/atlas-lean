# Bullshark: a DAG protocol with a partially synchronous fast path

Bullshark (with $n = 3f + 1$) consists of two protocols on the round-based DAG with different commit rules.

- *Asynchronous Bullshark* (Section 5) divides the DAG into waves of four rounds. Each wave has a predefined steady-state leader in round 1, a predefined steady-state leader in round 3, and a fallback leader in round 1 chosen retrospectively by the common coin in round 4. Each vertex votes either steady-state or fallback, its type being determined by whether its source committed a leader in the previous wave, and a vertex cannot vote for both types in one wave. A leader is committed directly when at least $2f + 1$ potential votes of the applicable type have strong paths to it: the strong edges of round-2 vertices for the first steady-state leader, round-4 vertices for the second steady-state leader and for the fallback leader. It keeps DAG-Rider's asynchronous liveness, amortized communication and safety without signatures in the ordering layer, and in synchronous periods it can commit a steady-state leader two rounds after it is proposed.
- *Partially synchronous Bullshark* (Section 6) has no fallback leaders; parties advance rounds with timeouts and commit the predefined leader of every second round when at least $f + 1$ vertices of the following round have strong paths to it. After GST, if the predefined leaders of two consecutive leader rounds are honest, the second of them is committed by all honest parties; the protocol needs no view-change or view-synchronization mechanism. Its steady-state latency thus requires an honest, supported leader after GST, not merely GST.

## Proof sketch

In the asynchronous protocol, if some party commits a leader with $2f + 1$ votes of one type, every other party sees at least $f + 1$ of these votes by quorum intersection and the non-equivocation of the DAG; since a vertex cannot vote for both types in a wave, at most $2f$ votes of the other type exist, so leaders of different types are never both committed in a wave. Parties order earlier leaders consistently by recomputing the same potential votes along strong paths from the last ordered leader. In the partially synchronous protocol there is only one leader type, and $f + 1$ strong-path votes in the next round suffice: every later committed leader has a strong path to such a leader by quorum intersection.

## Depends on

- [Round-based DAG of reliably broadcast vertices](round-based-byzantine-dag.md)
- [Partial synchrony](../../distributed-execution-models/partial-synchrony.md)
- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [DAG-Rider: asynchronous Byzantine atomic broadcast with zero extra communication for ordering](dag-rider-asynchronous-atomic-broadcast.md)
- [Cardinality conditions for threshold Byzantine quorum systems and masking-register safety](../byzantine-broadcast-and-quorum-systems/cardinality-conditions-for-threshold-byzantine-quorum-systems-and-masking-regist.md)

## Sources

- A. Spiegelman, N. Giridharan, A. Sonnino, L. Kokoris-Kogias, "Bullshark: DAG BFT Protocols Made Practical", ACM CCS 2022, arXiv:2201.05677, Sections 1, 5 and 6 and Appendix C.
- G. Danezis, L. Kokoris-Kogias, A. Sonnino, A. Spiegelman, "Narwhal and Tusk: A DAG-based Mempool and Efficient BFT Consensus", EuroSys 2022, arXiv:2105.11827.
