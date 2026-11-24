# Consensus under partial synchrony with benign faults

In Dwork, Lynch and Stockmeyer's basic model, in which processors are synchronous and communication is partially synchronous, consensus with fail-stop or omission faults is solvable for $N \ge 2t + 1$: their first algorithm, which proceeds in phases with a rotating coordinator and locking of values, satisfies agreement, strong unanimity and termination.

## Depends on

- [Partial synchrony](../distributed-execution-models/partial-synchrony.md)
- [Resilient consensus protocols](resilient-consensus-protocols.md)
- [Fail-stop, omission and Byzantine faults](../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- C. Dwork, N. Lynch and L. Stockmeyer, "Consensus in the presence of partial synchrony", *Journal of the ACM* 35(2):288–323, 1988
