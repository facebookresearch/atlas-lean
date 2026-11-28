# Immediate dominators from semidominators

In a flowgraph $G = (V, E, r)$ with a depth-first numbering, spanning tree $T$ and [semidominators](semidominators.md) $\mathrm{sdom}$, let $w \ne r$ and let $u$ be a vertex with $\mathrm{sdom}(w) \xrightarrow{+} u \xrightarrow{*} w$ whose semidominator is minimum among such vertices. Then

$$\mathrm{idom}(w) = \begin{cases} \mathrm{sdom}(w) & \text{if } \mathrm{sdom}(w) = \mathrm{sdom}(u),\\ \mathrm{idom}(u) & \text{otherwise.}\end{cases}$$

Since $u \xrightarrow{*} w$, $u \le w$, and $u \ne w$ in the second case. So the immediate dominators can be computed in increasing order of vertex number once all semidominators are known.

**Proof.** If $\mathrm{sdom}(u) = \mathrm{sdom}(w)$, the hypothesis of [the equality case](the-semidominator-is-the-immediate-dominator.md) holds. Otherwise $\mathrm{idom}(w) = \mathrm{idom}(u)$ by [the minimizing-vertex theorem](the-immediate-dominator-of-a-minimizing-vertex.md).

## Depends on

- [Semidominators](semidominators.md)

## Proof depends on

- [When the semidominator is the immediate dominator](the-semidominator-is-the-immediate-dominator.md)
- [The immediate dominator of a minimizing vertex](the-immediate-dominator-of-a-minimizing-vertex.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979, Section 2: Corollary 1 (equation (2)), from Theorems 2 and 3; Section 3, Steps 3 and 4 of the algorithm.
