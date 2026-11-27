# Maximum adjacency orderings

Let $f$ be a symmetric set function on a finite set $V$ with $|V| \ge 2$ (for a weighted graph, $f(X) = w(\delta(X))$). An ordering $v_1, \dots, v_n$ of $V$ is a **maximum adjacency (MA) ordering** of a weighted graph if each $v_{i+1}$ maximizes the total weight of edges to $\{v_1, \dots, v_i\}$ among the remaining vertices; for a general symmetric submodular $f$, $v_{i+1}$ minimizes $f(\{v_1, \dots, v_i\} \cup \{v\}) - f(\{v\})$. The last two vertices $(v_{n-1}, v_n)$ form a **pendent pair**.

## Depends on

- [Minimum cut size](../../../randomized-algorithms/karger-s-algorithm/is-min-cut.md)
- [Submodular set function](../../../approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- M. Stoer and F. Wagner, "A Simple Min-Cut Algorithm", Journal of the ACM 44(4), 1997.
- M. Queyranne, "Minimizing Symmetric Submodular Functions", Mathematical Programming 82, 1998.
