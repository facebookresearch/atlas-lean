# Lazy normalization of k-server algorithms

Every online $k$-server strategy $A$ on a metric space can be simulated by a *lazy* online strategy that, on each request, moves at most one server, and only when no server is at the requested point, and whose cost on every request sequence is at most that of $A$. The lazy strategy keeps its servers at a subset of the points that $A$'s servers have visited.

## Proof sketch

Track $A$'s virtual configuration. When a request is uncovered in the lazy configuration, move the lazy server corresponding to the virtual server that $A$ used to cover it; its travel is at most the virtual server's accumulated travel since its last lazy move, by the triangle inequality.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Online request-serving problem and competitive ratio](../competitive-analysis/online-problem-and-competitive-ratio.md)

## Sources

- M. S. Manasse, L. A. McGeoch and D. D. Sleator, "Competitive Algorithms for Server Problems", Journal of Algorithms 11(2), 1990.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
