# Election safety and log matching in Raft

Every execution of the Raft consensus protocol starting from the initial state (`State.init`)
satisfies the following invariants.

- *Election safety*: at most one leader is elected in each term.
- *Leader append-only*: a leader never overwrites or deletes entries in its log; it only appends new entries.
- *Log matching*: if two logs contain an entry with the same index and term, then the logs are identical in all entries up through that index.

Election safety follows because each server votes for at most one candidate in a term, its vote being recorded in persistent state, and a leader needs votes from a majority of the servers; log matching follows because a leader creates at most one entry with a given index in a given term and because of the consistency check of AppendEntries.

## Depends on

- [The Raft consensus protocol](the-raft-consensus-protocol.md)

## Sources

- D. Ongaro and J. Ousterhout, "In search of an understandable consensus algorithm", *USENIX ATC 2014*, <https://raft.github.io/raft.pdf>, Figure 3 and Sections 5.2 and 5.3
