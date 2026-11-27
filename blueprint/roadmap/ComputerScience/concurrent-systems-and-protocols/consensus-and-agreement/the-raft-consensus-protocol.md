# The Raft consensus protocol

Raft replicates a log of state-machine commands on a fixed cluster of servers. Servers fail by stopping and may later recover from stable storage; messages may be delayed, lost, duplicated or reordered. Each server is a *follower*, a *candidate* or a *leader*, and keeps

- *persistent state*, written to stable storage before it responds to any RPC: its current term `currentTerm` (initially $0$, increasing monotonically), the candidate `votedFor` that received its vote in the current term (or none), and its log, a sequence of entries indexed from $1$, each holding a command and the term in which the leader received it;
- *volatile state*: the index `commitIndex` of the highest entry known to be committed and the index `lastApplied` of the highest entry applied to its state machine, both initially $0$ and increasing monotonically, and, on a leader, for each other server the index `nextIndex` of the next entry to send and the index `matchIndex` of the highest entry known to be replicated there.

The rules are as follows.

- *All servers*: if `commitIndex` exceeds `lastApplied`, increment `lastApplied` and apply that entry; if an RPC request or response carries a term $T$ larger than `currentTerm`, set `currentTerm` to $T$, reset `votedFor` to none, and become a follower.
- *RequestVote* (term, candidate, index and term of the candidate's last entry): the receiver replies false if the term is below its `currentTerm`; otherwise it grants its vote if `votedFor` is none or this candidate and the candidate's log is at least as up to date as its own. Of two logs whose last entries have different terms the one with the later term is more up to date; if the last terms are equal the longer log is more up to date.
- *Candidates*: on becoming a candidate a server increments `currentTerm`, votes for itself, resets its election timer and sends RequestVote to all other servers; it becomes leader on receiving votes from a majority of the servers, and then sets, for every other server, `nextIndex` to its own last log index plus one and `matchIndex` to $0$; it becomes a follower on receiving AppendEntries from a new leader, and starts a new election if its election timeout elapses. A follower becomes a candidate when its election timeout elapses without an AppendEntries from the current leader and without granting a vote.
- *AppendEntries* (term, leader, index and term of the entry preceding the new ones, new entries, leader's `commitIndex`): the receiver replies false if the term is below its `currentTerm`, or if its log has no entry at the preceding index with the preceding term; it deletes any existing entry that conflicts with a new one (same index, different term) together with all that follow it, appends the new entries not already in its log, and, if the leader's `commitIndex` exceeds its own, sets `commitIndex` to the minimum of the leader's `commitIndex` and the matched index, the preceding index plus the number of new entries (the preceding index itself for an empty heartbeat).
- *Leaders*: a leader sends empty AppendEntries as heartbeats, appends each client command to its own log, sends each follower the entries from its `nextIndex` on, updating `nextIndex` and `matchIndex` on success and decrementing `nextIndex` and retrying on a log inconsistency, and sets `commitIndex` to $N$ whenever $N$ exceeds `commitIndex`, a majority of the servers, the leader included with its own last log index in place of a `matchIndex`, hold entries up to at least $N$, and the entry at $N$ has term `currentTerm`.

This is the protocol without cluster membership changes or log compaction.

## Sources

- D. Ongaro and J. Ousterhout, "In search of an understandable consensus algorithm", *USENIX ATC 2014*, <https://raft.github.io/raft.pdf>, Section 2, Figure 2 and Section 5.4.1
