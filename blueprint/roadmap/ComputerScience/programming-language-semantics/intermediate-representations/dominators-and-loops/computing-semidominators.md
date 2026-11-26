# Computing semidominators from edges and ancestors

In a flowgraph $G = (V, E, r)$ with a depth-first numbering and spanning tree $T$, the [semidominator](semidominators.md) of every vertex $w \ne r$ satisfies

$$\mathrm{sdom}(w) = \min\bigl(\{v \mid (v, w) \in E \text{ and } v < w\} \cup \{\mathrm{sdom}(u) \mid u > w \text{ and there is an edge } (v, w) \text{ with } u \xrightarrow{*} v\}\bigr).$$

The right-hand side refers only to semidominators of vertices numbered above $w$, so all semidominators can be computed in decreasing order of vertex number.

## Depends on

- [Semidominators](semidominators.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979: Section 2, Theorem 4 (equation (3)) and its proof; Section 3, Step 2 of the algorithm.
