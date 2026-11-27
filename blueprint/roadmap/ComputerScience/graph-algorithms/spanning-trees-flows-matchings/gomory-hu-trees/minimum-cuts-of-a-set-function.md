# Minimum s-t cuts of a set function

Let $V$ be a finite ground set and $f : 2^V \to \beta$ a set function into a linearly ordered abelian group. For distinct $s, t \in V$, a set $X \subseteq V$ is a **minimum $s$-$t$ cut** of $f$ if $s \in X$, $t \notin X$ and $f(X) \le f(Y)$ for every $Y$ with $s \in Y$, $t \notin Y$; write $\lambda_f(s, t) = f(X)$. $f$ is **symmetric** if $f(V \setminus X) = f(X)$ for all $X$. The motivating example is the cut function $X \mapsto w(\delta(X))$ of an undirected graph with nonnegative edge weights $w$, which is symmetric and submodular.

## Depends on

- [Submodular set function](../../../approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [Source–sink cut](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/is-stcut.md)

## Sources

- R. E. Gomory and T. C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics 9(4), 1961.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
