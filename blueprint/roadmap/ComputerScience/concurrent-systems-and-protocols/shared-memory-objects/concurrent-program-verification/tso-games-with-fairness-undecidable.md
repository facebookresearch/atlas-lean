# Games on programs under TSO semantics are undecidable with fairness

When the execution of a concurrent program under total store order is viewed as a game between a player choosing instructions and a player choosing when buffered writes reach memory, safety games with process fairness and reachability games with update fairness are undecidable.

**Setting (Spengler).** A TSO program consists of finitely many finite-state processes over shared variables with a finite data domain; under total store order each process has an unbounded FIFO buffer of pending writes, and buffered messages are updated to the shared memory at nondeterministic times. A program induces a game: in configurations owned by the *process player* $A$ she executes an instruction of some process, and in configurations owned by the *update player* $B$ he updates any number of buffered messages (possibly none) to memory; the two alternate. A play that ends in a deadlock is won by the player who did not get stuck. A set of local states induces the target configurations, those in which some process is in such a state. In a *reachability game* $A$ wins plays reaching a target configuration; in a *safety game* she wins plays avoiding them. *Process fairness* requires that every process enabled infinitely often on $A$'s turns executes infinitely often; *update fairness* requires that whenever the program is deadlocked on $A$'s turn, all buffers are empty. The reachability (safety) problem asks whether the initial configuration is winning for $A$, where in the safety game with process fairness $A$ must also play fairly, and in the reachability game with update fairness $A$ also wins every play on which $B$ violates update fairness.

**Theorem (Spengler).**

1. The safety problem for TSO games with process fairness is undecidable.
2. The reachability problem for TSO games with update fairness is undecidable.

Without these fairness conditions, the same paper reduces both problems to games on single-process programs and states that they are PSPACE-complete, leaving the proofs of both bounds to its extended version (Section 6).

## Depends on

- [The x86-TSO abstract machine](../../weak-memory-models/the-x86-tso-abstract-machine.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Both proofs reduce from state reachability in perfect channel systems, finite-state machines with an unbounded reliable FIFO channel, which is undecidable. The buffer of one process stores the channel contents; a protocol between two processes rotates messages through the buffer and memory using memory fences and an auxiliary variable, so that each channel message is received once and only once. The fairness conditions are what forces the opponent to complete each rotation, so that the game simulates the channel system faithfully, and the winning condition is induced by the final states of the channel system.

A good expansion links pages for the undecidability of the channel-system problem the reduction starts from, and for the rotation protocol that lets one process buffer simulate the channel.

## Sources

- Stephan Spengler, "Reachability and Safety Games under TSO Semantics", Proceedings of the Fifteenth International Symposium on Games, Automata, Logics, and Formal Verification (GandALF 2024), EPTCS 409, pp. 154–171, 2024, <https://doi.org/10.4204/EPTCS.409.14>; Section 4 (games), Section 5 (TSO games, with Theorem 4 reducing them to single-process games), Section 6 (decidability and PSPACE-completeness without fairness), Theorem 8 of Section 7 (update fairness in reachability games) and Theorem 9 of Section 8 (process fairness in safety games) of arXiv:2411.00847v1, read at <https://arxiv.org/abs/2411.00847v1>.
