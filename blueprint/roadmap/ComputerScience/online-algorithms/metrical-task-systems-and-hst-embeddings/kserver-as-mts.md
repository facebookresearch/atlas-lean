# k-server is a metrical task system on configurations

The $k$-server problem on an $n$-point metric $(M,d)$ is the metrical task system on the state space of $k$-element configurations $\binom{M}{k}$ (or multisets) with the minimum-cost matching distance, where a request $r$ is the cost function that is $0$ on configurations containing $r$ and $+\infty$ elsewhere. Consequently an $f(N)$-competitive MTS algorithm on $N$-point metrics yields an $f\big(\binom{n}{k}\big)$-competitive $k$-server algorithm.

## Proof sketch

Serving $r$ requires a configuration containing $r$, which is exactly finite service cost; moving between configurations costs their matching distance, which is a metric on configurations. Costs and feasibility coincide step by step, and competitive ratios transfer verbatim.

## Depends on

- [Metrical task systems](metrical-task-system.md)

## Proof depends on

- [Metrical task systems](metrical-task-system.md)

## Sources

- Allan Borodin, Nathan Linial, Michael E. Saks, "An Optimal On-Line Algorithm for Metrical Task System", Journal of the ACM 39(4) (1992).
- Mark S. Manasse, Lyle A. McGeoch, Daniel D. Sleator, "Competitive Algorithms for Server Problems", Journal of Algorithms 11(2) (1990).
