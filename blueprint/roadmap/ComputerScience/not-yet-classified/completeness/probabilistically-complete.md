# Probabilistically complete planner

A randomized path planner on a metric configuration space, driven by a probability measure, is probabilistically complete if (1) it is sound: every path it reports is a solution and it reports \"no path\" only for unsolvable problems; (2) on every robustly feasible problem, the probability that it has found a path by step $N$ tends to $1$ as $N \to \infty$; and (3) for every problem and every $N$, the event of having found a path by step $N$ is measurable.

## Sources

- S. M. LaValle, *Planning Algorithms*, Cambridge University Press, 2006, Ch. 4.3.1 (Formulation 4.1) and Ch. 5 introduction.
