# Three-phase commit is nonblocking under crashes but not under partitions

Three-phase commit inserts a committable pre-commit state between uncertain and committed, ensuring that no operational site is uncertain while another site has committed. Under site crashes with reliable failure detection, the operational sites can then terminate with Skeen's central-site termination protocol: a backup coordinator chosen among them decides from its own state alone, aborting if it is in the initial, uncertain (wait) or aborted state and committing if it is pre-committed or committed (exactly when the concurrency set of its state contains a commit state). Before announcing the decision it moves every operational site to its own state and waits for their acknowledgements, so that a later backup, elected if this one crashes, reaches the same decision. This preserves agreement and abort validity and lets the operational sites terminate. No commit protocol, however, is resilient to network partitions: if two disjoint groups must each terminate independently after a partition, some execution forces them to decide differently.

## Proof sketch

The pre-commit buffer state guarantees that no site is in a noncommittable state (initial, uncertain or aborted) while another site has committed, and that no site is pre-committed or committed while another has aborted, so the backup's own state determines a safe decision; moving every operational site to that state first ensures that any later backup's state leads to the same decision. For partitions, a group containing a pre-committed site and a group containing only uncertain sites have no communication and incompatible safe choices.

## Depends on

- [Atomic commitment and blocking of two-phase commit](../atomic-commitment-and-blocking-of-two-phase.md)
- [Two-phase commit blocks: uncertain survivors cannot terminate safely](two-phase-commit-blocks-uncertain-survivors-cannot-terminate-safely.md)

## Sources

- Dale Skeen, "Nonblocking Commit Protocols", Proceedings of the 1981 ACM SIGMOD International Conference on Management of Data, 1981, Section 7 (central site termination).
- Dale Skeen and Michael Stonebraker, "A Formal Model of Crash Recovery in a Distributed System", IEEE Transactions on Software Engineering, 1983.
