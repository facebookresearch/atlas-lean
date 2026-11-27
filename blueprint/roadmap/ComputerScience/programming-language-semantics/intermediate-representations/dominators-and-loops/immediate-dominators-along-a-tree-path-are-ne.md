# Immediate dominators along a tree path are nested

Let $G = (V, E, r)$ be a flowgraph with a depth-first spanning tree $T$, as in [semidominators](semidominators.md), and write $x \xrightarrow{*} y$ when $x$ is an ancestor of $y$ in $T$. If $v$ and $w$ are vertices other than $r$, so that both have immediate dominators, and $v \xrightarrow{*} w$, then $v \xrightarrow{*} \mathrm{idom}(w)$ or $\mathrm{idom}(w) \xrightarrow{*} \mathrm{idom}(v)$.

**Proof.** Let $x$ be a proper descendant of $\mathrm{idom}(v)$ that is also a proper ancestor of $v$. Some path from $r$ to $v$ avoids $x$; followed by the tree path from $v$ to $w$, it gives a path from $r$ to $w$ that avoids $x$. So $\mathrm{idom}(w)$ is not such an $x$; being an ancestor of $w$, it is a descendant of $v$ or an ancestor of $\mathrm{idom}(v)$.

## Depends on

- [Semidominators](semidominators.md)

## Proof depends on

- [The immediate dominator is a proper tree ancestor](the-immediate-dominator-is-a-proper-tree-ances.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979, Section 2, Lemma 5 with its proof.
