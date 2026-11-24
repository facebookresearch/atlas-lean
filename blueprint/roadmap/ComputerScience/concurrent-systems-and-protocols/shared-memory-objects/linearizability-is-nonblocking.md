# Linearizability is nonblocking

If $\mathit{inv}$ is a pending invocation of a total operation in a linearizable history $H$, then there is a matching response $\mathit{res}$ such that $H \cdot \mathit{res}$ is linearizable. Hence linearizability never forces a process with a pending total operation to wait for another process.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Linearizability.

## Sources

- M. P. Herlihy and J. M. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM Transactions on Programming Languages and Systems* 12(3):463–492, 1990, Theorem 2
