# Atomic commitment and blocking of two-phase commit

A distributed transaction has a coordinator and participants. Each process $p_i$ has a vote $\mathit{vote}_i \in \{\mathit{Yes}, \mathit{No}\}$ and may decide $\mathit{decision}_i \in \{\mathit{Commit}, \mathit{Abort}\}$. An *atomic commitment protocol* must satisfy:
- **AC-1:** all processes that reach a decision reach the same one;
- **AC-2:** no process reverses its decision;
- **AC-3:** Commit is decided only if all processes voted Yes;
- **AC-4:** if there are no failures and all vote Yes, the decision is Commit;
- **AC-5:** if all failures are repaired and no new ones occur, all processes eventually decide.

A process is *uncertain* if it has voted Yes but does not yet know the decision.

**Two-phase commit (2PC).**
1. The coordinator sends a vote request to all participants.
2. Each participant sends its vote. A participant voting No decides Abort and stops.
3. If all votes are Yes, the coordinator decides Commit and sends Commit to all. Otherwise it decides Abort and sends Abort to those that voted Yes.
4. A participant that voted Yes decides whatever it receives.

On timeouts:
- a participant still waiting for the vote request may decide Abort;
- the coordinator waiting for votes may decide Abort;
- a participant that voted Yes and waits for the decision cannot decide alone, and must run a termination protocol.

**Theorem.**
1. 2PC satisfies AC-1 to AC-4.
2. 2PC *blocks*. Suppose all participants voted Yes and the coordinator crashes before any participant learns the decision. Then every operational participant is uncertain and cannot decide until the coordinator recovers, even without communication failures among the operational processes.
3. More generally, if communication failures or total failures are possible, every atomic commitment protocol may cause processes to block. No protocol can guarantee that failed processes recover independently.

**Proof sketch.**
1. Commit is decided only by the coordinator after all Yes votes and is relayed unchanged, which gives AC-1 and AC-3. Decisions are final, which gives AC-2. Without failures, the run reaches step 3 with all Yes votes, which gives AC-4.
2. In the scenario, every operational participant's local history is the same whether the crashed coordinator had decided Commit or Abort. Asking each other does not help, because none of them knows. Deciding either value could contradict the coordinator's decision and violate AC-1.

## Background

- [Atomicity between participants](atomicity.md)
- [Validity for participants](committed-imp-all-voted-yes.md)

## Sources

- L. Alvisi, *Atomic Commit*, lecture notes, CS 371D Distributed Computing, University of Texas at Austin, Fall 2008, <https://www.cs.utexas.edu/~lorenzo/corsi/cs371d/08F/notes/week3.pdf>: the model (coordinator, participants, votes, decisions, transaction log), the specification AC-1 to AC-5, uncertainty and independent recovery, Proposition 1 (with communication or total failures, every atomic commitment protocol may block) and Proposition 2 (no protocol guarantees independent recovery), the 2PC protocol (steps I–IV), the notes that 2PC satisfies AC-1 to AC-4 but not AC-5 as is, the timeout actions and termination protocols, and the remark that 2PC can block even with non-total failures and no communication failures among operating processes.
