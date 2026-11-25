# FLP impossibility of asynchronous consensus with agreement, validity and termination

Let the set of processes be finite with at least two processes, and let $f \ge 1$. No deterministic asynchronous message-passing algorithm solves consensus tolerating $f$ crash faults. Solving consensus means: in every state reachable from an input assignment all decided values agree and each is the input of some process; and in every admissible run with at most $f$ faulty processes (a run from an initial state in which every process is faulty or receives every message that is ever in flight to it) every process is faulty or decides at some time.

**Model.** Asynchronous: no clocks, no bounds on relative speeds or message delays. Communication: a reliable unordered message buffer; a fair run delivers every message to a process that is not faulty. Failures: crash; a process is faulty in a run when at some time a message to it is in flight and from then on it receives nothing. Processes are deterministic and a step is the receipt of one message (or a stuttering step that changes nothing).

**Relation to the source.** The correctness condition is stronger than the one of Fischer, Lynch and Paterson, who require only partial correctness (agreement, and both decision values reachable) and that some process decides in every admissible run. An impossibility for a stronger requirement is a weaker theorem, so this is weaker than their Theorem 1; their statement is [FLP impossibility of asynchronous consensus, original form](flp-original.md). With one process the hypothesis fails and consensus is trivial.

## Related topics

- [FLP impossibility of asynchronous consensus, original form](flp-original.md): the stronger original statement, in the same model, by the original bivalence argument.

## Sources

- M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one faulty process*, Journal of the ACM 32(2), 1985, 374–382: Theorem 1.
- H. Völzer, *A constructive proof for FLP*, Information Processing Letters 92(2), 2004, 83–87 (formalized in CSLib; not read for this page).
- The formal proof, in the CSLib formalization of the FLP theorem (`Cslib.FLP.Consensus.ge_one_not_exists`), follows Völzer's constructive proof.
