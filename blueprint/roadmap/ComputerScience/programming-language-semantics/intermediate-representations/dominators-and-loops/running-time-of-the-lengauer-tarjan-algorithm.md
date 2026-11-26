# Running time of the Lengauer–Tarjan algorithm

The Lengauer–Tarjan algorithm computes the immediate dominator of every vertex other than $r$ of a flowgraph $G = (V, E, r)$ with $n \ge 2$ vertices and $m$ edges in four steps:
1. a depth-first search numbers the vertices and builds the spanning tree;
2. [semidominators are computed](computing-semidominators.md) in decreasing order of number;
3. each immediate dominator is defined implicitly by the [rule relating it to semidominators](immediate-dominators-from-semidominators.md);
4. the immediate dominators are made explicit in increasing order of number.

The minima over tree paths that steps 2 and 3 need are evaluated on a forest that starts with every vertex as a single-vertex tree, each vertex $v$ carrying its current label $\mathrm{semi}(v)$, initially its own number. $\mathrm{LINK}(v, w)$ adds the edge from $w$ to its tree parent $v$, and $\mathrm{EVAL}(v)$ returns $v$ if $v$ is the root of its tree, and otherwise a vertex of minimum current label on the path from $v$ up to the root of its tree, $v$ included and the root excluded. A label is the final semidominator only once the vertex has been processed: on $r(1) \to a(2) \to b(3)$, while $b$ is processed, $\mathrm{EVAL}(a)$ returns $a$ with current label $2$, not $\mathrm{sdom}(a) = 1$.
- With path compression alone, the algorithm runs in time $O(m \log n)$.
- With path compression on balanced trees, linking by subtree size, it runs in time $O(m\,\alpha(m, n))$, where $\alpha(m, n) = \min\{i \ge 1 \mid A(i, \lfloor 2m/n \rfloor) > \log_2 n\}$ for the Ackermann-type function $A$ on integers $i, j \ge 0$ with $A(i, 0) = 0$, $A(0, j) = 2^j$ for $j \ge 1$, $A(i, 1) = A(i - 1, 2)$ for $i \ge 1$, and $A(i, j) = A(i - 1, A(i, j - 1))$ for $i \ge 1$, $j \ge 2$.

## Depends on

- [Computing semidominators from edges and ancestors](computing-semidominators.md)
- [Immediate dominators from semidominators](immediate-dominators-from-semidominators.md)

## Expansion

This page becomes ready once this prerequisite is stated:

- Bounds for evaluating minima on paths in trees: $m$ operations $\mathrm{EVAL}$ and $n - 1$ operations $\mathrm{LINK}$ take time $O(m \log n)$ with path compression and $O(m\,\alpha(m, n))$ with path compression on balanced trees (proof prerequisite; Tarjan, "Applications of path compression on balanced trees", *Journal of the ACM* 26(4):690–715, 1979, as cited by Lengauer and Tarjan).

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979: the abstract and Section 1 (the $O(m \log n)$ and $O(m\,\alpha(m, n))$ bounds and the definition of $\alpha$), Section 3 (Steps 1–4 and the tree operations they use).
