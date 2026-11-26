# k-server on $k+1$ points is a metrical task system

On a metric space $(M, d)$ with $|M| = k + 1$, the $k$-server problem is equivalent to the metrical task system on $(M, d)$ whose state is the unique point not covered by a server: moving a server from $a$ to the uncovered point $b$ changes the state from $b$ to $a$ at cost $d(a, b)$, and a request at $r$ is the cost function that is $+\infty$ at state $r$ and $0$ elsewhere. Competitive ratios of the two problems on $(M,d)$ coincide.

## Proof sketch

Configurations of $k$ servers on $k+1$ points correspond bijectively to their complements, and a lazy algorithm moves one server at a time, which corresponds to a single move of the hole. The matching distance between two configurations equals the distance between their holes, and serving a request at $r$ means the hole is not at $r$.

## Depends on

- [Metrical task systems](../metrical-task-systems-and-hst-embeddings/metrical-task-system.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Sources

- Sébastien Bubeck, Christian Coester, Yuval Rabani, "The Randomized k-Server Conjecture Is False!", STOC (2023), arXiv:2211.05753.
- Mark S. Manasse, Lyle A. McGeoch, Daniel D. Sleator, "Competitive Algorithms for Server Problems", Journal of Algorithms 11(2) (1990).
