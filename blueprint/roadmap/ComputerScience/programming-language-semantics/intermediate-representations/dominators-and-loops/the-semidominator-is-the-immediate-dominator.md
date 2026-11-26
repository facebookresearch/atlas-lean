# When the semidominator is the immediate dominator

Let $G = (V, E, r)$ be a flowgraph with a depth-first numbering and spanning tree $T$, as in [semidominators](semidominators.md), and write $x \xrightarrow{+} y$ and $x \xrightarrow{*} y$ for proper and arbitrary ancestry in $T$. Let $w \ne r$. If every vertex $u$ with $\mathrm{sdom}(w) \xrightarrow{+} u \xrightarrow{*} w$ satisfies $\mathrm{sdom}(u) \ge \mathrm{sdom}(w)$, then $\mathrm{idom}(w) = \mathrm{sdom}(w)$.

**Proof idea.** Since $\mathrm{idom}(w)$ is an ancestor of $\mathrm{sdom}(w)$, it suffices that $\mathrm{sdom}(w)$ dominates $w$; this is clear if $\mathrm{sdom}(w) = r$. Otherwise consider a path from $r$ to $w$, the last vertex $x$ on it numbered below $\mathrm{sdom}(w)$, and the first vertex $y$ after $x$ with $\mathrm{sdom}(w) \xrightarrow{*} y \xrightarrow{*} w$. By the [paths lemma](paths-lemma-for-depth-first-search.md) the vertices strictly between $x$ and $y$ are numbered above $y$, so $\mathrm{sdom}(y) \le x < \mathrm{sdom}(w)$, and the hypothesis forces $y = \mathrm{sdom}(w)$. So every path from $r$ to $w$ passes through $\mathrm{sdom}(w)$.

## Depends on

- [Semidominators](semidominators.md)

## Proof depends on

- [Paths lemma for depth-first search](paths-lemma-for-depth-first-search.md)
- [The immediate dominator is an ancestor of the semidominator](the-immediate-dominator-is-an-ancestor-of-the.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979, Section 2, Theorem 2 with its proof.
