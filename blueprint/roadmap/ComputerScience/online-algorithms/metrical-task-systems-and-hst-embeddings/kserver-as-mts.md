# k-server is a metrical task system on configurations

The $k$-server problem on an $n$-point metric $(M,d)$ with $n \ge k$, started from $k$ distinct points, is the metrical task system on the state space $\binom{M}{k}$ of $k$-element subsets (servers at distinct points) with the minimum-cost matching distance, where a request $r$ is the cost function that is $0$ on configurations containing $r$ and $+\infty$ elsewhere. Distinct configurations lose nothing, because lazy algorithms, which move only one server to an uncovered request, are as good as arbitrary ones and never put two servers on one point. Consequently an $f(N)$-competitive MTS algorithm on $N$-point metrics yields an $f\big(\binom{n}{k}\big)$-competitive $k$-server algorithm; with multisets as states the count is $\binom{n+k-1}{k}$ instead (for $n = 3$, $k = 2$: six multisets but three subsets).

## Proof sketch

Serving $r$ requires a configuration containing $r$, which is exactly finite service cost; moving between configurations costs their matching distance, which is a metric on configurations. Costs and feasibility coincide step by step, and competitive ratios transfer verbatim.

## Depends on

- [Metrical task systems](metrical-task-system.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Matching distance between server configurations](../k-server-on-the-line/matching-distance-between-configurations.md)

## Proof depends on

- [Lazy normalization of k-server algorithms](../k-server-on-the-line/lazy-normalization-of-k-server-algorithms.md)

## Sources

- Allan Borodin, Nathan Linial, Michael E. Saks, "An Optimal On-Line Algorithm for Metrical Task System", Journal of the ACM 39(4) (1992).
- Mark S. Manasse, Lyle A. McGeoch, Daniel D. Sleator, "Competitive Algorithms for Server Problems", Journal of Algorithms 11(2) (1990).
