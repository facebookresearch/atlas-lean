# The quadratic lower bound is tight for Byzantine consensus under partial synchrony

Under partial synchrony with $n = 3f + 1$ processes, at most $f$ of them Byzantine, an authenticated point-to-point network and a $(2f + 1, n)$-threshold signature scheme, and with all correct processes starting by GST, there is a deterministic Byzantine consensus protocol (SQuad) with $O(n^2)$ communication complexity and $O(f)$ latency complexity, matching the Dolev–Reischuk lower bound $\Omega(n^2)$. Its validity is the one to which that bound applies: if all correct processes propose the same value $v$, then only $v$ can be decided. SQuad uses two threshold schemes: an $(f + 1, n)$-threshold scheme in a certification phase and the $(2f + 1, n)$-threshold scheme for the quorum certificates of the consensus core Quad, which alone guarantees only weak validity. Here the communication complexity of an execution is the number of words sent by all correct processes during $[\mathrm{GST}, t_d]$, where $t_d$ is the first time by which all correct processes have decided (zero if $t_d < \mathrm{GST}$), a word holds a constant number of signatures and values, and the protocol's complexity is the maximum over executions; the latency complexity is $\max(0, t_d - \mathrm{GST})$.

## Proof sketch

Quad combines the HotStuff view core, in which each view costs $O(n)$ words through a leader-to-all, all-to-leader pattern with $(2f + 1, n)$-threshold certificates, with the view synchronizer RareSync, and ensures only weak validity (if all processes are correct, a decided value was proposed). SQuad adds a preceding certification phase (Section 5.2, Algorithm 4): each process broadcasts its proposal with a partial signature on it, and $f + 1$ partial signatures on a value $v$ combine into an $(f + 1, n)$-threshold signature, a constant-size certificate for $v$; a process that receives $2f + 1$ disclosures without $f + 1$ for a common value instead signs the string "any value", and $f + 1$ such shares form a certificate valid for every value. If all correct processes propose $v$, at most $f$ processes can sign another value and no correct process signs "any value", so no certificate for another value exists; and every correct process eventually obtains some certificate. This phase costs $O(n^2)$ words and $O(1)$ latency. SQuad then runs a certificate-validating Quad in which every value is accompanied by its certificate and values without one are ignored, which gives the validity above. RareSync groups views into epochs of $f + 1$ views; processes advance through the views of an epoch using local timers only and perform a single all-to-all exchange of $O(n^2)$ words at the end of each epoch. After GST all correct processes enter a common epoch within $O(f)$ time and then stay synchronized, and each correct process enters only a constant number of epochs during $[\mathrm{GST}, t_d]$. With at most $f$ faulty leaders, a correct leader's view is reached within that epoch, so the view core contributes $n \cdot O(n)$ words and the synchronizer $O(n^2)$ words.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)
- [Quorum certificate from threshold signatures](quorum-certificate-threshold-signatures.md)

## Proof depends on

- [Byzantine agreement requires quadratic communication](dolev-reischuk-quadratic-lower-bound.md)
- [Chained HotStuff with locking and three-phase commit](hotstuff-protocol-three-phase.md)

## Sources

- P. Civit, M. A. Dzulfikar, S. Gilbert, V. Gramoli, R. Guerraoui, J. Komatovic, M. Vidigueira, "Byzantine Consensus Is Θ(n²): The Dolev-Reischuk Bound Is Tight Even in Partial Synchrony!", DISC (2022), Section 5 (Theorems 3 and 4, Algorithms 4 and 5), doi:10.4230/LIPIcs.DISC.2022.14.
