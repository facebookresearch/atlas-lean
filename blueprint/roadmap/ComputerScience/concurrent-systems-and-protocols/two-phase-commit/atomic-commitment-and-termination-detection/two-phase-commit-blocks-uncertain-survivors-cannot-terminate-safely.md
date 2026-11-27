# Two-phase commit blocks: uncertain survivors cannot terminate safely

In fail-stop two-phase commit, with uniform agreement, abort validity on any "no" vote and failure-free commit nontriviality as the atomic commitment specification, decisions are stable, all deciding sites agree, any "no" vote forces abort, and failure-free runs with all "yes" votes commit. However, when the coordinator crashes while every surviving cohort is uncertain (has voted "yes" but not received a decision), both commit and abort remain consistent with what survivors can observe, so no termination rule run by the survivors alone is safe.

## Proof sketch

The crashed coordinator may have decided commit after receiving all yes votes, or abort; both runs give identical survivor views, so any survivor decision violates agreement in one of them.

## Depends on

- [Atomic commitment and blocking of two-phase commit](../atomic-commitment-and-blocking-of-two-phase.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- Jim Gray, "Notes on Data Base Operating Systems", Operating Systems: An Advanced Course, Springer, 1978.
- Dale Skeen, "Nonblocking Commit Protocols", Proceedings of the 1981 ACM SIGMOD International Conference on Management of Data, 1981.
- Dale Skeen and Michael Stonebraker, "A Formal Model of Crash Recovery in a Distributed System", IEEE Transactions on Software Engineering, 1983.
