# Consensus under partial synchrony with benign faults

In Dwork, Lynch and Stockmeyer's basic model, in which processors are synchronous and communication is partially synchronous, consensus with fail-stop or omission faults is solvable for $N \ge 2t + 1$: their first algorithm, which proceeds in phases with a rotating coordinator and locking of values, satisfies agreement, strong unanimity and termination.

## Depends on

- [Partial synchrony](../distributed-execution-models/partial-synchrony.md)

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Consensus specification with agreement, strong unanimity and termination.
- Statement prerequisite: Dwork–Lynch–Stockmeyer fail-stop and omission fault models.

## Sources

- C. Dwork, N. Lynch and L. Stockmeyer, "Consensus in the presence of partial synchrony", *Journal of the ACM* 35(2):288–323, 1988
