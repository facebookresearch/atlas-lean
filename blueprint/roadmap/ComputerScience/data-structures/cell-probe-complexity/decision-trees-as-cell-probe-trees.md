# Boolean decision trees are read-only one-bit cell-probe trees

Identify assignments $x \in \{0,1\}^S$ with memories of $S$ one-bit cells. Every Boolean decision tree $T$ over the variables $x_1, \dots, x_S$ with leaf values in $R$ is realized by a read-only cell-probe tree $T'$ over $S$ cells of width $w = 1$ such that, on every assignment $x$, $T'$ returns the value of $T$ on $x$, its number of probes equals the number of variables queried by $T$ on $x$, the set of probed cells equals the set of queried variables, and $\operatorname{depth}(T') = \operatorname{depth}(T)$.

## Proof sketch

Replace each query node on $x_i$ by a read node on cell $i$ whose two children are the translations of the two subtrees; leaves are unchanged. Each claim follows by structural induction.

## Depends on

- [Adaptive cell-probe decision tree](adaptive-cell-probe-decision-tree.md)
- [Boolean function computed by a decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/eval.md)

## Sources

- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), pp. 21-43, 2002.
