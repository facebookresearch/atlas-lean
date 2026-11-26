# Immediate dominators from semidominators

In a flowgraph $G = (V, E, r)$ with a depth-first numbering, spanning tree $T$ and [semidominators](semidominators.md) $\mathrm{sdom}$, let $w \ne r$.

1. If every $u$ with $\mathrm{sdom}(w) \xrightarrow{+} u \xrightarrow{*} w$ satisfies $\mathrm{sdom}(u) \ge \mathrm{sdom}(w)$, then $\mathrm{idom}(w) = \mathrm{sdom}(w)$.
2. Let $u$ be a vertex with $\mathrm{sdom}(w) \xrightarrow{+} u \xrightarrow{*} w$ whose semidominator is minimum among such vertices. Then $\mathrm{sdom}(u) \le \mathrm{sdom}(w)$ and $\mathrm{idom}(u) = \mathrm{idom}(w)$.
3. Consequently, for such a $u$,

    $$\mathrm{idom}(w) = \begin{cases} \mathrm{sdom}(w) & \text{if } \mathrm{sdom}(w) = \mathrm{sdom}(u),\\ \mathrm{idom}(u) & \text{otherwise.}\end{cases}$$

Since $u \xrightarrow{*} w$, $u \le w$, and $u \ne w$ in the second case of part 3. So part 3 lets the immediate dominators be computed in increasing order of vertex number once all semidominators are known.

## Depends on

- [Semidominators](semidominators.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979: Section 2, Theorem 2, Theorem 3 and Corollary 1 (equation (2)), with Lemma 5; Section 3, Steps 3 and 4 of the algorithm.
