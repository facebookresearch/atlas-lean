# No dispute wheel implies solvability

If an instance of the [stable paths problem](the-stable-paths-problem.md) has no [dispute wheel](dispute-wheels.md), then it is solvable. The proof runs a greedy procedure that grows a stable partial assignment from $V_0 = \{0\}$, adding at each step the nodes whose highest-ranked path consistent with the current assignment is a direct path into it; if the procedure gets stuck before covering $V$, following, from a stuck node, a higher-ranked permitted path that is not direct, then the next stuck node, and so on, eventually closes a dispute wheel.

## Depends on

- [The stable paths problem](the-stable-paths-problem.md)
- [Dispute wheels](dispute-wheels.md)

## Sources

- T. G. Griffin, F. B. Shepherd and G. Wilfong, "The stable paths problem and interdomain routing", *IEEE/ACM Transactions on Networking* 10(2):232–243, 2002, Section V.B (the greedy procedure) and Section V.C, Theorem V.3 with its proof. The source notes that BAD BACKUP is solvable and yet has a dispute wheel, so the converse fails.
