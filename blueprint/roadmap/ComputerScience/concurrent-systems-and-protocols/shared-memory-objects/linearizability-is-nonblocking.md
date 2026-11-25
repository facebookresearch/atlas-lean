# Linearizability is nonblocking

If $\mathit{inv}$ is a pending invocation of a total operation in a linearizable history $H$, then there is a matching response $\mathit{res}$ such that $H \cdot \mathit{res}$ is linearizable. Hence linearizability never forces a process with a pending total operation to wait for another process.

## Depends on

- [Linearizability](linearizability.md)

## Sources

- M. P. Herlihy and J. M. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM Transactions on Programming Languages and Systems* 12(3):463–492, 1990, Theorem 2
