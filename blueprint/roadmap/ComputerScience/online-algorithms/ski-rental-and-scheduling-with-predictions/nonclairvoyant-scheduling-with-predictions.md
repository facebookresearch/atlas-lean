# Non-clairvoyant scheduling with predicted job sizes

In *non-clairvoyant single-machine scheduling*, $n$ jobs are available at time $0$ with unknown processing times $p_1, \dots, p_n \ge 1$, preemption is free, and the objective is the total completion time $\sum_j C_j$; a job's size is revealed only when it completes. With predictions, the algorithm also receives predicted sizes $y_1, \dots, y_n$, with error $\eta = \sum_j |p_j - y_j|$. The offline optimum, which knows the processing times, runs the jobs to completion one after another in shortest-processing-time order; preemption does not lower the optimal total completion time when all jobs are available at time $0$.

## Depends on

- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Proof depends on

- [Shortest processing time first minimizes total completion time](../../greedy-algorithms-and-matroids/single-machine-scheduling/shortest-processing-time-first-minimizes-total.md)

## Sources

- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018).
- Rajeev Motwani, Steven Phillips, Eric Torng, "Nonclairvoyant Scheduling", Theoretical Computer Science 130(1) (1994).
