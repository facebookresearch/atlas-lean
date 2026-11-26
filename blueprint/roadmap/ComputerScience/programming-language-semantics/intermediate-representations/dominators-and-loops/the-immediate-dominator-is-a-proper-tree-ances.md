# The immediate dominator is a proper tree ancestor

Let $G = (V, E, r)$ be a flowgraph with a depth-first spanning tree $T$, as in [semidominators](semidominators.md). For every vertex $w \ne r$, the immediate dominator $\mathrm{idom}(w)$ is a proper ancestor of $w$ in $T$.

**Proof.** Every dominator of $w$ lies on the path in $T$ from $r$ to $w$.

## Depends on

- [Semidominators](semidominators.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979, Section 2, Lemma 2 with its proof.
