# The quadratic lower bound is tight for Byzantine consensus under partial synchrony

Under partial synchrony with $n = 3f + 1$ processes, at most $f$ of them Byzantine, an authenticated point-to-point network and a $(2f + 1, n)$-threshold signature scheme, and with all correct processes starting by GST, there is a deterministic Byzantine consensus protocol (SQuad) with $O(n^2)$ communication complexity and $O(f)$ latency complexity, matching the Dolev–Reischuk lower bound $\Omega(n^2)$. Here the communication complexity of an execution is the number of words sent by all correct processes during $[\mathrm{GST}, t_d]$, where $t_d$ is the first time by which all correct processes have decided (zero if $t_d < \mathrm{GST}$), a word holds a constant number of signatures and values, and the protocol's complexity is the maximum over executions; the latency complexity is $\max(0, t_d - \mathrm{GST})$.

## Proof sketch

SQuad combines the HotStuff view core, in which each view costs $O(n)$ words through a leader-to-all, all-to-leader pattern with threshold-signature certificates, with the view synchronizer RareSync. RareSync groups views into epochs of $f + 1$ views; processes advance through the views of an epoch using local timers only and perform a single all-to-all exchange of $O(n^2)$ words at the end of each epoch. After GST all correct processes enter a common epoch within $O(f)$ time and then stay synchronized, and each correct process enters only a constant number of epochs during $[\mathrm{GST}, t_d]$. With at most $f$ faulty leaders, a correct leader's view is reached within that epoch, so the view core contributes $n \cdot O(n)$ words and the synchronizer $O(n^2)$ words.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)
- [Quorum certificate from threshold signatures](quorum-certificate-threshold-signatures.md)

## Proof depends on

- [Byzantine agreement requires quadratic communication](dolev-reischuk-quadratic-lower-bound.md)
- [Chained HotStuff with locking and three-phase commit](hotstuff-protocol-three-phase.md)

## Sources

- P. Civit, M. A. Dzulfikar, S. Gilbert, V. Gramoli, R. Guerraoui, J. Komatovic, M. Vidigueira, "Byzantine Consensus Is Θ(n²): The Dolev-Reischuk Bound Is Tight Even in Partial Synchrony!", DISC (2022), Theorem 4, doi:10.4230/LIPIcs.DISC.2022.14.
