# Partial persistence for bounded in-degree pointer structures

Every pointer-machine data structure whose nodes have in-degree bounded by a constant can be made partially persistent (all past versions can be queried, the newest can be updated) with $O(1)$ amortized time overhead per primitive pointer-machine access or update step, so that every operation is slowed down by at most a constant factor, and $O(1)$ amortized extra space per update step, by the node-copying method of Driscoll, Sarnak, Sleator and Tarjan.

## Proof depends on

- [Potential method: amortized costs bound actual costs](../../amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- J. R. Driscoll, N. Sarnak, D. D. Sleator and R. E. Tarjan, "Making data structures persistent", *Journal of Computer and System Sciences* 38(1):86–124, 1989
- E. Demaine, *Advanced Data Structures*, MIT 6.851 lecture notes, Spring 2012
