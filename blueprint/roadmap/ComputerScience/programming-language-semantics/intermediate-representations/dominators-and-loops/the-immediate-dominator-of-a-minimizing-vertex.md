# The immediate dominator of a minimizing vertex

Let $G = (V, E, r)$ be a flowgraph with a depth-first numbering and spanning tree $T$, as in [semidominators](semidominators.md), and write $x \xrightarrow{+} y$ and $x \xrightarrow{*} y$ for proper and arbitrary ancestry in $T$. Let $w \ne r$ and let $u$ be a vertex with $\mathrm{sdom}(w) \xrightarrow{+} u \xrightarrow{*} w$ whose semidominator is minimum among such vertices. Then $\mathrm{sdom}(u) \le \mathrm{sdom}(w)$ and $\mathrm{idom}(u) = \mathrm{idom}(w)$.

**Proof idea.** Taking $u$ the child of $\mathrm{sdom}(w)$ on the tree path to $w$, or $u = w$, shows $\mathrm{sdom}(u) \le \mathrm{sdom}(w)$. By [the nesting lemma](immediate-dominators-along-a-tree-path-are-ne.md), $\mathrm{idom}(w)$ is a descendant of $u$ or an ancestor of $\mathrm{idom}(u)$, and the first is excluded by [the ancestor lemma](the-immediate-dominator-is-an-ancestor-of-the.md). It remains that $\mathrm{idom}(u)$ dominates $w$, shown with the [paths lemma](paths-lemma-for-depth-first-search.md) as for [the case of equality](the-semidominator-is-the-immediate-dominator.md).

## Depends on

- [Semidominators](semidominators.md)

## Proof depends on

- [Paths lemma for depth-first search](paths-lemma-for-depth-first-search.md)
- [The immediate dominator is an ancestor of the semidominator](the-immediate-dominator-is-an-ancestor-of-the.md)
- [Immediate dominators along a tree path are nested](immediate-dominators-along-a-tree-path-are-ne.md)
- [When the semidominator is the immediate dominator](the-semidominator-is-the-immediate-dominator.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979, Section 2, Theorem 3 with its proof.
