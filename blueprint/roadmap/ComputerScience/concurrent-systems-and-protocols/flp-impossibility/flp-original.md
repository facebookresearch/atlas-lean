# FLP impossibility of asynchronous consensus, original form

Let the set of processes be finite with at least two processes, and let $a$ be a partially correct algorithm: no state reachable from an input assignment has decided two different values, and each value $b$ is decided in some state reachable from some input assignment. Then some admissible run of $a$ with at most one faulty process never decides: no process decides at any time. This is Theorem 1 of Fischer, Lynch and Paterson ("no consensus protocol is totally correct in spite of one fault"), in the model of these pages.

**Model.** As in [FLP impossibility of asynchronous consensus with agreement, validity and termination](flp-impossibility.md): asynchronous, a reliable unordered message buffer with fair delivery to processes that are not faulty, crash faults, deterministic processes. The model differs from that of Fischer, Lynch and Paterson in three respects: in their model a step may receive the null message, so a process can always take a step on its own, whereas here every step other than the stuttering step, which changes nothing, receives a message (a protocol can emulate spontaneous steps with messages to itself); a process holds its input in an input register there, whereas here the input is delivered to it as a message, in flight in the initial state; and a process is faulty there when it takes only finitely many steps, whereas here it is faulty when at some time a message to it is in flight and from then on it receives nothing. The proof below works directly in this model, not by transfer from theirs.

**Strength.** Partial correctness asks less than the consensus condition of [FLP impossibility of asynchronous consensus with agreement, validity and termination](flp-impossibility.md) (no validity, and only some process must decide), so this statement implies that one for $f = 1$. The hypotheses are satisfiable: in an algorithm where one fixed process decides its own input when it receives it and no other process ever decides, partial correctness holds; there the theorem's run is, for instance, one in which that process never receives its input.

**Proof.** As in the source. Suppose every admissible run decides. Then a decision is reachable from every reachable state without any one process; Lemma 2 gives a bivalent initial state; and Lemma 3, applied stage by stage along a fair order of the pending messages, delivers every pending message while returning to a bivalent state at the end of each stage. The run so built is admissible and never decides, since a decided reachable state is not bivalent (by agreement).

## Informally uses

- [Deciding runs give reachable decisions](pseudo-termination-of-forall-decides.md): the termination property used by the lemmas, from the contradiction hypothesis.
- [A bivalent initial state](exists-bivalent-start.md): Lemma 2, the start of the run.
- [A bivalent configuration survives any pending event](exists-bivalent-recv-msg.md): Lemma 3, each stage of the run.

## Sources

- M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one faulty process*, Journal of the ACM 32(2), 1985, 374–382: §2 (model, partial correctness, admissible and deciding runs), Theorem 1 and its proof.
