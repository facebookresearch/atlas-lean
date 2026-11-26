# Three-phase commit is nonblocking under crashes but not under partitions

Three-phase commit inserts a committable pre-commit state between uncertain and committed, ensuring that no operational site is uncertain while another site has committed. Under crash failures with reliable failure detection, survivors can then terminate by polling: abort if some survivor is uncertain or aborted, otherwise commit; this preserves agreement and abort validity and always terminates. No commit protocol, however, is resilient to network partitions: if two disjoint groups must each terminate independently after a partition, some execution forces them to decide differently.

## Proof sketch

The pre-commit buffer state guarantees that the global state never contains both an uncertain and a committed site, so survivors' views determine a safe decision. For partitions, a group containing a pre-committed site and a group containing only uncertain sites have no communication and incompatible safe choices.

## Depends on

- [Atomic commitment and blocking of two-phase commit](../atomic-commitment-and-blocking-of-two-phase.md)
- [Two-phase commit blocks: uncertain survivors cannot terminate safely](two-phase-commit-blocks-uncertain-survivors-cannot-terminate-safely.md)

## Sources

- Dale Skeen, "Nonblocking Commit Protocols", Proceedings of the 1981 ACM SIGMOD International Conference on Management of Data, 1981.
- Dale Skeen and Michael Stonebraker, "A Formal Model of Crash Recovery in a Distributed System", IEEE Transactions on Software Engineering, 1983.
