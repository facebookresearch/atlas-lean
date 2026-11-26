# Atomic commitment and blocking of two-phase commit

A distributed transaction has a coordinator and a set $P$ of participants. Each process $p_i$ has a vote $\mathit{vote}_i \in \{\mathit{Yes}, \mathit{No}\}$ and may decide $\mathit{decision}_i \in \{\mathit{Commit}, \mathit{Abort}\}$. An *atomic commitment protocol* must satisfy:
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
- a participant that voted Yes and waits for the decision cannot decide alone, and must run a termination protocol: it waits for the coordinator to recover, or it runs the cooperative termination protocol and asks another participant $q$, and decides as $q$ did if $q$ has decided; if $q$ has not voted, $q$ decides Abort, which the asker can then learn; if $q$ is uncertain, the asker learns nothing.

Every process keeps its state in a log on stable storage and may crash and recover. A recovering coordinator keeps its decision, or decides Abort if it had not decided; a recovering participant keeps its state, or decides Abort if it had not voted.

**Model.** The coordinator is waiting, committed or aborted, and each participant is working (not yet voted), prepared (voted Yes and uncertain), committed or aborted. The coordinator has no vote of its own, so all processes voted Yes when all participants did, and a prepared or committed participant has voted Yes. Messages are abstracted into guards on the global state: the coordinator decides Commit when every participant is prepared, and, other than on a timeout, decides Abort only when some participant has aborted; a participant that has not voted may also learn an Abort; a participant learns the coordinator's decision only while both are operational, so a crash of the coordinator loses the decision messages not yet delivered. Messages between operational processes are not lost, and a timeout may occur at any time. A run is *failure-free* if it has no crash, recovery, timeout or termination step.

**Theorem.** For every set $P$ of participants:
1. 2PC satisfies AC-1 to AC-4:
    - **AC-1:** in every reachable state, no participant has committed while another has aborted, the coordinator has not committed while a participant has aborted, and it has not aborted while a participant has committed;
    - **AC-2:** along every finite run, from any state, every process that has decided Commit or Abort keeps that decision;
    - **AC-3:** in every reachable state in which the coordinator or some participant has committed, every participant is prepared or committed;
    - **AC-4:** in every state reached from the initial state by a failure-free run in which no participant votes No, no process has aborted; and if no protocol step other than a No vote can be taken there, the coordinator and every participant have committed.
2. 2PC *blocks*. From every state in which every participant is prepared and the coordinator has crashed, every finite run in which the coordinator does not recover leaves every participant prepared: no participant decides until the coordinator recovers, although the operational participants may ask each other for the decision.

**Proof sketch.**
1. Every reachable state satisfies the invariant that a committed coordinator has only prepared or committed participants and that a committed participant has a committed coordinator; this gives AC-1 and AC-3. No step changes a decided state, which gives AC-2. In a failure-free run without No votes no participant aborts, so the coordinator never aborts, and every process stays operational; a state in which no participant can vote Yes, the coordinator cannot commit and no participant can learn the commit is one in which everybody has committed, which gives AC-4.
2. While the coordinator is crashed, a prepared participant can change its state only by learning a decision from another participant, and every other participant is prepared too. The operational participants cannot do better: their states are the same whether the coordinator decided Commit or, on a timeout, Abort before it crashed, so deciding either value could contradict the coordinator's decision.

## Background

- [Atomicity between participants](atomicity.md)
- [Validity for participants](committed-imp-all-voted-yes.md)

## Sources

- L. Alvisi, *Atomic Commit*, lecture notes, CS 371D Distributed Computing, University of Texas at Austin, Fall 2008, <https://www.cs.utexas.edu/~lorenzo/corsi/cs371d/08F/notes/week3.pdf>: the model (coordinator, participants, votes, decisions, transaction log), the specification AC-1 to AC-5, uncertainty, the 2PC protocol (steps I–IV), the notes that 2PC satisfies AC-1 to AC-4 but not AC-5 as is, the timeout actions, the termination protocols (waiting for the coordinator, cooperative termination), the logging actions and the recovery rules, and the remark that 2PC can block even with non-total failures and no communication failures among operating processes.
