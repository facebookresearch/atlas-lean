# Running time of the Lengauer–Tarjan algorithm

The Lengauer–Tarjan algorithm computes the immediate dominator of every vertex of a flowgraph $G = (V, E, r)$ with $n$ vertices and $m$ edges in four steps:
1. a depth-first search numbers the vertices and builds the spanning tree;
2. [semidominators are computed](computing-semidominators.md) in decreasing order of number;
3. each immediate dominator is defined implicitly by the [rule relating it to semidominators](immediate-dominators-from-semidominators.md);
4. the immediate dominators are made explicit in increasing order of number.

The minima over tree paths that steps 2 and 3 need are evaluated with a data structure for functions defined on paths in trees, with operations that link a vertex to its tree parent and that evaluate the minimum semidominator on the path from a vertex to the root of its tree in the forest built so far.
- With a simple implementation of these operations, the algorithm runs in time $O(m \log n)$.
- With a more sophisticated implementation, it runs in time $O(m\,\alpha(m, n))$, where $\alpha(m, n) = \min\{i \ge 1 \mid A(i, \lfloor 2m/n \rfloor) > \log_2 n\}$ for the Ackermann-type function $A$ on integers $i, j \ge 0$ with $A(i, 0) = 0$, $A(0, j) = 2^j$ for $j \ge 1$, $A(i, 1) = A(i - 1, 2)$ for $i \ge 1$, and $A(i, j) = A(i - 1, A(i, j - 1))$ for $i \ge 1$, $j \ge 2$.

## Depends on

- [Computing semidominators from edges and ancestors](computing-semidominators.md)
- [Immediate dominators from semidominators](immediate-dominators-from-semidominators.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979: the abstract and Section 1 (the $O(m \log n)$ and $O(m\,\alpha(m, n))$ bounds and the definition of $\alpha$), Section 3 (Steps 1–4 and the tree operations they use).
