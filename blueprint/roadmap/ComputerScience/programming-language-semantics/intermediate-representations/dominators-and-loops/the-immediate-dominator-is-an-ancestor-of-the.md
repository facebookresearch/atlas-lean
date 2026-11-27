# The immediate dominator is an ancestor of the semidominator

Let $G = (V, E, r)$ be a flowgraph with a depth-first numbering and spanning tree $T$, as in [semidominators](semidominators.md). For every vertex $w \ne r$, $\mathrm{idom}(w)$ is an ancestor, not necessarily proper, of $\mathrm{sdom}(w)$ in $T$.

**Proof.** Both are proper ancestors of $w$. The path that follows $T$ from $r$ to $\mathrm{sdom}(w)$ and then a path $\mathrm{sdom}(w) = v_0, \dots, v_k = w$ with $v_i > w$ for $0 < i < k$ avoids every proper descendant of $\mathrm{sdom}(w)$ that is a proper ancestor of $w$, since such vertices are numbered below $w$. So $\mathrm{idom}(w)$, which lies on every path from $r$ to $w$, is an ancestor of $\mathrm{sdom}(w)$.

## Depends on

- [Semidominators](semidominators.md)

## Proof depends on

- [The immediate dominator is a proper tree ancestor](the-immediate-dominator-is-a-proper-tree-ances.md)
- [The semidominator is a proper tree ancestor](the-semidominator-is-a-proper-tree-ancestor.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979, Section 2, Lemma 4 with its proof.
