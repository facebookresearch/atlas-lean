# Three-phase commit is nonblocking under crashes but not under partitions

Three-phase commit inserts a committable pre-commit state between uncertain and committed, ensuring that no operational site is uncertain while another site has committed. Under site crashes with reliable failure detection, the operational sites can then terminate with Skeen's central-site termination protocol: a backup coordinator chosen among them decides from its own state alone, aborting if it is in the initial, uncertain (wait) or aborted state and committing if it is pre-committed or committed (exactly when the concurrency set of its state contains a commit state). Before announcing the decision it moves every operational site to its own state and waits for their acknowledgements, so that a later backup, elected if this one crashes, reaches the same decision. This preserves agreement and abort validity and lets the operational sites terminate. Under network partitions, if messages in transit when the partition occurs are lost, no commit protocol is resilient to a partition into two groups (Skeen 1982, Theorem 4.4); with multiple partitions none is resilient even when undeliverable messages are returned to the sender (Theorem 4.8).

## Proof sketch

The pre-commit buffer state guarantees that no site is in a noncommittable state (initial, uncertain or aborted) while another site has committed, and that no site is pre-committed or committed while another has aborted, so the backup's own state determines a safe decision; moving every operational site to that state first ensures that any later backup's state leads to the same decision. For partitions, a group containing a pre-committed site and a group containing only uncertain sites have no communication and incompatible safe choices.

## Depends on

- [Atomic commitment and blocking of two-phase commit](../atomic-commitment-and-blocking-of-two-phase.md)
- [Two-phase commit blocks: uncertain survivors cannot terminate safely](two-phase-commit-blocks-uncertain-survivors-cannot-terminate-safely.md)

## Sources

- Dale Skeen, "Nonblocking Commit Protocols", Proceedings of the 1981 ACM SIGMOD International Conference on Management of Data, 1981, Section 5 (central site termination protocol), pp. 140–141.
- Dale Skeen and Michael Stonebraker, "A Formal Model of Crash Recovery in a Distributed System", IEEE Transactions on Software Engineering, 1983.
- Dale Skeen, "Crash Recovery in a Distributed Database System", PhD dissertation, Memorandum No. UCB/ERL M82/45, University of California, Berkeley, 1982, Section 4.2 (Theorems 4.4 and 4.8) and Section 5.4.1 (Lemma 5.8 and Theorem 5.9).
