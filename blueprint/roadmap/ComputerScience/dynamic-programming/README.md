# Dynamic programming

Optimization problems solved by tabulated recurrences: knapsack variants, subset sum, rod cutting, matrix-chain ordering, optimal binary search trees, longest common and longest increasing subsequences (including patience sorting) and maximum subarray (Kadane and divide-and-conquer); string edit distance goes to String algorithms.

- [Deterministic finite-horizon control problem](control-problem.md)
- [Admissible sequence of a deterministic control problem](is-admissible-sequence.md)
- [Total cost of a control sequence from a stage](total-cost.md)
- [Backward-induction values](backward-value.md)
- [Backward induction for deterministic finite-horizon control](deterministic-finite-horizon-dynamic-programming.md)
- [Vertices of the stage-indexed graph](stage-vertex.md)
- [Arcs of the stage-indexed graph](stage-arc.md)
- [Arc lengths of the stage-indexed graph](stage-arc-length.md)
- [The stage-indexed graph is acyclic](stage-arc-acyclic.md)
- [Longest common subsequence](longest-common-subsequence/README.md)
- [Longest increasing subsequence](longest-increasing-subsequence/README.md)
- [Matrix chain multiplication](matrix-chain-multiplication/README.md)
- [Maximum subarray problem](maximum-subarray-problem/README.md)
- [Multiple-choice knapsack problem](multiple-choice-knapsack-problem/README.md)
- [Optimal binary search tree](optimal-binary-search-tree/README.md)
- [Rod cutting](rod-cutting/README.md)
- [Subset sum](subset-sum/README.md)
- [Weighted interval scheduling](weighted-interval-scheduling/README.md)
- [Weighted interval scheduling: exchange identity](weighted-interval-scheduling-exchange-identity/README.md)
- [Zero-one knapsack problem](zero-one-knapsack-problem/README.md)
- [Dynamic Programming over Tree Decompositions](tree-decomposition-dynamic-programming/README.md)
- [Exact Exponential and Parameterized Algorithms](exact-exponential-and-fpt-algorithms/README.md)
- [The Knuth-Yao Quadrangle-Inequality Speedup](knuth-yao-quadrangle-inequality-speedup/README.md)

## Related topics

- [Value iteration](../heuristic-search-and-planning/value-iteration/README.md): dynamic programming over an infinite horizon, where the recurrence becomes Bellman's equation, a fixed-point equation solved by iterating the Bellman operator.
- [Policy iteration](../heuristic-search-and-planning/policy-iteration/README.md): the other classical method for Bellman's equation, alternating policy evaluation and greedy improvement.
- [Stochastic shortest path problems](../heuristic-search-and-planning/stochastic-shortest-path-problems/README.md): undiscounted dynamic programming with a termination state, which contains deterministic shortest paths.
- [Optimality of stationary policies](../heuristic-search-and-planning/optimality-of-stationary-policies/README.md): the finite-horizon DP algorithm for Markov decision processes, whose backward recursion gives the best $N$-stage value of a Markov policy.
- [Dynamic programming principles](dynamic-programming-principles/README.md)
