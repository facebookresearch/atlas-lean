# Raft

Raft, the consensus protocol of Ongaro and Ousterhout, replicates a log of state-machine commands on a fixed finite cluster of servers that fail by stopping and may recover from stable storage, over a network that may delay, lose, duplicate and reorder messages. Here it is the labelled transition system of their Figure 2, without cluster membership changes or log compaction. Its states are the states of the servers, each with its persistent `currentTerm`, `votedFor` and log and its volatile role, `commitIndex`, `lastApplied`, `nextIndex`, `matchIndex` and granted votes, together with the multiset of messages in flight. Its steps are election timeouts at any moment, elections by a majority of votes, client requests to leaders, replication by AppendEntries, a leader's advance of `commitIndex` to an index $N$ whose entry has the leader's current term when a majority of the servers have `matchIndex` at least $N$, the leader counting itself with its last log index, application of the entries up to `commitIndex`, the receipt of RequestVote and AppendEntries requests and responses, the loss and duplication of messages, crashes, which keep only the persistent state, and recoveries. Initialized runs are its traces from the state in which every server is an up follower of term $0$ with an empty log and no message is in flight; the transition system itself also admits traces from other states. The main statement gives every rule and convention.

## Idea

Raft splits consensus into leader election, log replication and safety. Time is divided into terms, which act as a logical clock: a server that sees a newer term adopts it and becomes a follower. A follower that hears nothing times out and runs for leader in a new term. Each server votes at most once in a term, recording its vote on stable storage, and only for a candidate whose log is at least as up to date as its own; a candidate needs the votes of a majority. The leader appends client commands to its log and replicates them with AppendEntries, whose check on the preceding entry makes a follower's log agree with the leader's up to the new entries; the leader advances its `commitIndex` only to an entry of its current term, once its `matchIndex` shows that a majority of the servers hold the entries up to it, which also covers the earlier entries, and servers apply the entries up to their `commitIndex` in log order. Safety does not depend on timing: timeouts only decide when progress is made. The statements give the protocol, a basic invariant, a run in which the rules make progress, and the safety properties.

## Statements

- [The Raft consensus protocol](the-raft-consensus-protocol.md)
- [Terms never decrease in Raft](current-term-le-of-m-tr.md): a basic invariant, crashes included.
- [A single-server Raft cluster elects itself and commits a command](exists-m-tr-commit-of-subsingleton.md): the rules allow an election, a commitment and an application.
- [Election safety and log matching in Raft](election-safety-and-log-matching-in-raft.md): the first safety properties.
- [Leader completeness and state machine safety in Raft](leader-completeness-and-state-machine-safety-in.md): the safety of the replicated state machine.

## Sources

- D. Ongaro and J. Ousterhout, "In search of an understandable consensus algorithm", in *Proceedings of the 2014 USENIX Annual Technical Conference (USENIX ATC '14)*, 2014, pp. 305–319, <https://www.usenix.org/conference/atc14/technical-sessions/presentation/ongaro>; extended version <https://raft.github.io/raft.pdf>, in which the items cited here have the same numbers: Section 5, Figure 2 and Figure 3.
