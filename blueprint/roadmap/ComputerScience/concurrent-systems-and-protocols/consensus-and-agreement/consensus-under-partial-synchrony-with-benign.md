# Consensus under partial synchrony with benign faults

In Dwork, Lynch and Stockmeyer's basic round model, in which processors proceed in synchronous rounds and messages sent in a round may be lost until an unknown global stabilization round after which every message between correct processors is delivered in its round, consensus with fail-stop or omission faults is solvable for $N \ge 2t + 1$: their Algorithm 1, which proceeds in phases with a rotating coordinator and locking of values, satisfies agreement, strong unanimity and termination in that model.

## Depends on

- [Partial synchrony](../distributed-execution-models/partial-synchrony.md)
- [Resilient consensus protocols](resilient-consensus-protocols.md)
- [Fail-stop, omission and Byzantine faults](../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- C. Dwork, N. Lynch and L. Stockmeyer, "Consensus in the presence of partial synchrony", *Journal of the ACM* 35(2):288–323, 1988
