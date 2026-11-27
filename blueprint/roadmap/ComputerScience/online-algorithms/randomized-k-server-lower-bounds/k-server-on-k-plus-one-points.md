# k-server on $k+1$ points is a metrical task system

Let $(M, d)$ be a metric space with $|M| = k + 1$, and consider $k$-server on $(M, d)$ from an initial configuration of $k$ distinct points. Every algorithm can be made lazy (move only when the request is uncovered, and then only one server, to the request) without increasing its cost, and a lazy algorithm keeps its $k$ servers on $k$ distinct points, so its configuration is determined by the unique uncovered point, the *hole*. Lazy $k$-server on $(M, d)$ is then the same as the metrical task system on $(M, d)$ whose state is the hole and whose tasks are restricted to the cost functions $c_r$ that are $+\infty$ at $r$ and $0$ elsewhere: moving a server from $a$ to the hole $b$ changes the state from $b$ to $a$ at cost $d(a, b)$, and a request at $r$ is the task $c_r$. Hence the competitive ratio of $k$-server on $(M, d)$ equals that of this restricted metrical task system, and it is at most that of the metrical task system on $(M, d)$ with arbitrary tasks.

## Proof sketch

Configurations of $k$ distinct points among $k+1$ points correspond bijectively to their complements, and a lazy algorithm moves one server at a time, which corresponds to a single move of the hole; without the distinctness, two servers on one point would leave two uncovered points and no single state. The matching distance between two configurations equals the distance between their holes, and serving a request at $r$ means the hole is not at $r$.

## Depends on

- [Metrical task systems](../metrical-task-systems-and-hst-embeddings/metrical-task-system.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Sources

- Sébastien Bubeck, Christian Coester, Yuval Rabani, "The Randomized k-Server Conjecture Is False!", STOC (2023), arXiv:2211.05753, Proposition 8.
- Mark S. Manasse, Lyle A. McGeoch, Daniel D. Sleator, "Competitive Algorithms for Server Problems", Journal of Algorithms 11(2) (1990).
