# The semidominator is a proper tree ancestor

Let $G = (V, E, r)$ be a flowgraph with a depth-first numbering and spanning tree $T$, as in [semidominators](semidominators.md). For every vertex $w \ne r$, $\mathrm{sdom}(w)$ is a proper ancestor of $w$ in $T$.

**Proof.** The tree parent of $w$ is joined to $w$ by an edge and is numbered below $w$, so $\mathrm{sdom}(w) < w$. Take a path $\mathrm{sdom}(w) = v_0, \dots, v_k = w$ with $v_i > w$ for $0 < i < k$. By the [paths lemma](paths-lemma-for-depth-first-search.md) some $v_i$ is a common ancestor of $\mathrm{sdom}(w)$ and $w$; it satisfies $v_i \le \mathrm{sdom}(w)$, so $i = 0$, and $\mathrm{sdom}(w)$ is a proper ancestor of $w$.

## Depends on

- [Semidominators](semidominators.md)

## Proof depends on

- [Paths lemma for depth-first search](paths-lemma-for-depth-first-search.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979, Section 2, Lemma 3 with its proof.
