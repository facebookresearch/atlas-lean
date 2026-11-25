# Leader completeness and state machine safety in Raft

In Raft, with the rule that a candidate receives a vote only if its log is at least as up to date as the voter's, and the commitment rule under which a leader considers an entry committed by counting replicas only for entries of its current term: (leader completeness) every entry committed in a term is present in the logs of the leaders of all higher terms; and (state machine safety) no two servers apply different commands at the same log index.

## Depends on

- [The Raft consensus protocol](the-raft-consensus-protocol.md)

## Proof depends on

- [Election safety and log matching in Raft](election-safety-and-log-matching-in-raft.md)

## Sources

- D. Ongaro and J. Ousterhout, "In search of an understandable consensus algorithm", *USENIX ATC 2014*, <https://raft.github.io/raft.pdf>, Figure 3 and Section 5.4
