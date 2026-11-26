# Paths lemma for depth-first search

Let $G = (V, E, r)$ be a flowgraph whose vertices are numbered in the order in which a depth-first search from $r$ first reaches them, with spanning tree $T$, as in [semidominators](semidominators.md). If $v$ and $w$ are vertices with $v \le w$, then every path from $v$ to $w$ in $G$ contains a common ancestor of $v$ and $w$ in $T$.

## Depends on

- [Semidominators](semidominators.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979, Section 2, Lemma 1 (the paths lemma), stated there with a reference to R. E. Tarjan, "Depth-first search and linear graph algorithms", *SIAM Journal on Computing* 1(2):146–160, 1972.
