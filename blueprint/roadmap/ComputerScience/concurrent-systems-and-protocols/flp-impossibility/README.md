# FLP impossibility

The theorem of Fischer, Lynch and Paterson (1985): in an asynchronous message-passing system no deterministic consensus protocol tolerates even one crash fault. The model on these pages: no clocks and no bounds on speeds or message delays; a reliable, unordered message buffer, with every message to a process that is not faulty eventually delivered in a fair run; crash faults, a process being faulty in a run when at some time a message to it is in flight and from then on it receives nothing; inputs delivered as messages in flight in the initial state; deterministic processes with write-once decisions. A step receives one message in flight, or is a stuttering step that changes nothing. The theorem is stated in two forms: for algorithms that solve consensus with agreement, validity and termination of every process that is not faulty, and in the original, stronger form, with the three lemmas of the original bivalence proof.

- [FLP impossibility of asynchronous consensus with agreement, validity and termination](flp-impossibility.md)
- [Valence of a state](valent.md)
- [Bivalent state](bivalent.md)
- [Commutativity of disjoint schedules](m-tr-comm.md)
- [A bivalent initial state](exists-bivalent-start.md)
- [Reachability without an event](reach-without.md)
- [A bivalent configuration survives any pending event](exists-bivalent-recv-msg.md)
- [Deciding runs give reachable decisions](pseudo-termination-of-forall-decides.md)
- [FLP impossibility of asynchronous consensus, original form](flp-original.md)

## Related topics

- [Two-phase commit](../two-phase-commit/README.md): a commit protocol; by the theorem every asynchronous commit protocol has a "window of vulnerability" in which one slow or crashed process can block it.
- [Byzantine agreement](../byzantine-agreement/README.md): consensus in synchronous rounds, where crash faults are tolerable but Byzantine faults need $n > 3m$.
- [Labelled transition systems](../../process-calculi/labelled-transition-systems/README.md): an algorithm of this model is a labelled transition system whose labels are message receipts and the stuttering step.
- [Synchronous consensus with crash failures](../synchronous-consensus-with-crash-failures/README.md): with synchrony consensus tolerates crashes, but $f$ crashes cost $f + 1$ rounds.
- [Paxos consensus](../paxos-consensus/README.md): in this asynchronous crash-failure setting Paxos keeps safety (at most one value chosen) unconditionally and gives up guaranteed termination, as the theorem requires.

## Sources

- M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one faulty process*, Journal of the ACM 32(2), 1985, 374–382: Theorem 1 and Lemmas 1–3.
- The first form is proved in the CSLib formalization of the FLP theorem following H. Völzer, *A constructive proof for FLP*, Information Processing Letters 92(2), 2004, 83–87 (not read for these pages).
