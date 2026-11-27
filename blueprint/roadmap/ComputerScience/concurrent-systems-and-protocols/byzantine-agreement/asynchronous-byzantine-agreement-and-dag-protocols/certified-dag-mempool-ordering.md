# Separating data dissemination from ordering: certified DAG mempools

In the Narwhal certified DAG mempool with $n = 3f + 1$ processes, each vertex (block) of round $r$ becomes certified once $2f + 1$ processes acknowledge storing it, and the certificate of availability (not the data) is referenced by round-$(r+1)$ vertices. Since any set of $2f + 1$ and any set of $f + 1$ processes out of $3f + 1$ intersect, every certified vertex is available: its data is stored by at least $f + 1$ correct processes and can always be retrieved, and the causal history of a certified vertex is available. A certificate proves availability only; it does not by itself make any ordering protocol progress. Narwhal can be combined with a partially synchronous consensus protocol (Narwhal-HotStuff), which orders certificates and is live only after GST, or with Tusk, a zero-message asynchronous ordering rule that interprets the DAG with a common coin. In Tusk the randomness of the third round of a wave selects a leader of its first round, which is committed when at least $f + 1$ vertices of the second round reference it; under an asynchronous adversary Tusk commits a leader every $7$ rounds of the DAG in expectation (Lemma 4), and with random message delays each block is committed in $4.5$ rounds in expectation (Lemma 5). (For $n > 3f + 1$ the thresholds $2f + 1$ and $f + 1$ must be adjusted, e.g. to $n - f$ and $n - 2f$, for these intersections to hold.)

## Proof sketch

Availability is quorum intersection: a certificate carries $2f + 1$ storage acknowledgements, at least $f + 1$ from correct processes. Since vertices reference certified predecessors, the causal history of any certified vertex is available, and ordering only certificates decouples ordering cost from batch size. In Tusk, the $f + 1$ second-round vertices that would satisfy the commit rule for some first-round vertex are fixed before the adversary learns the leader, so a leader is committed in each wave with probability at least $(f+1)/(3f+1) > 1/3$, which gives the bound in expectation.

## Depends on

- [Round-based DAG of reliably broadcast vertices](round-based-byzantine-dag.md)
- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [Cardinality conditions for threshold Byzantine quorum systems and masking-register safety](../byzantine-broadcast-and-quorum-systems/cardinality-conditions-for-threshold-byzantine-quorum-systems-and-masking-regist.md)
- [DAG-Rider: asynchronous Byzantine atomic broadcast with zero extra communication for ordering](dag-rider-asynchronous-atomic-broadcast.md)

## Sources

- G. Danezis, L. Kokoris-Kogias, A. Sonnino, A. Spiegelman, "Narwhal and Tusk: A DAG-based Mempool and Efficient BFT Consensus", EuroSys 2022, arXiv:2105.11827, Sections 3 and 5 (Lemmas 4 and 5).
