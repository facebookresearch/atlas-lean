# Consensus under partial synchrony needs a majority

In a partially synchronous system with fail-stop faults, for $N \ge 2$ processes and $t \ge 1$, there is no $t$-resilient consensus protocol when $N \le 2t$: the processes can be split into two groups of at most $t$ each that, before the global stabilization time, cannot distinguish an execution in which the other group has crashed from one in which its messages are delayed, so they decide different values.

## Depends on

- [Partial synchrony](../distributed-execution-models/partial-synchrony.md)

## Expansion

This page becomes ready once:

- Unresolved prerequisite named by review: consensus specification and admissible failures (statement prerequisite; not yet stated)

## Sources

- C. Dwork, N. Lynch and L. Stockmeyer, "Consensus in the presence of partial synchrony", *Journal of the ACM* 35(2):288–323, 1988
