# The coverability tree

Extend markings with a symbol $\omega$ such that $\omega > n$ and $\omega \pm n = \omega$ for every integer $n$, and $\omega \ge \omega$. The *coverability tree* of a [Petri net](place-transition-petri-nets.md) $(N, M_0)$ is built as follows.

1. Label the initial marking $M_0$ as the root and tag it "new".
2. While "new" markings exist, select one, $M$:
   - if $M$ is identical to a marking on the path from the root to $M$, tag it "old";
   - otherwise, if no transition is enabled at $M$, tag it "dead-end";
   - otherwise, for each transition $t$ enabled at $M$, obtain the marking $M'$ that results from firing $t$ at $M$; if some marking $M''$ on the path from the root to $M$ satisfies $M' \ge M''$ and $M' \ne M''$, replace $M'(p)$ by $\omega$ for every $p$ with $M'(p) > M''(p)$; then add $M'$ as a child of $M$ with an arc labelled $t$, and tag it "new".

The *coverability graph* has as nodes the distinct labels of the tree, with an arc labelled $t$ from $M_i$ to $M_j$ whenever $M_i [t\rangle M_j$. For a bounded net the tree and graph are the reachability tree and the [reachability graph](reachability-set-and-reachability-graph.md).

## Depends on

- [Place/transition Petri nets](place-transition-petri-nets.md)
- [Reachability set and reachability graph](reachability-set-and-reachability-graph.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section V-A ("The coverability tree"): the symbol $\omega$, Steps 1–2.4.3 of the construction, and the definition of the coverability graph.
