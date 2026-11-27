# The coverability tree

Extend the natural numbers with a symbol $\omega$ such that $\omega > n$ and $\omega + n = \omega - n = \omega$ for every natural number $n$, and $\omega \ge \omega$. An *$\omega$-marking* assigns to each place a natural number or $\omega$; $\omega$-markings are ordered placewise. A transition $t$ of a [Petri net](../place-transition-petri-nets.md) is enabled at an $\omega$-marking $M$ if $M(p) \ge w(p, t)$ for every input place $p$ of $t$, and firing it yields the $\omega$-marking $M'$ with $M'(p) = M(p) - w(p, t) + w(t, p)$ for every place $p$, so that $M'(p) = \omega$ exactly when $M(p) = \omega$.

The *coverability tree* of $(N, M_0)$ is the tree with nodes labelled by $\omega$-markings and arcs labelled by transitions built as follows, in which every node is processed exactly once.

1. Create a root labelled $M_0$ and tag it "new".
2. While some node is tagged "new", choose such a node $x$, labelled $M$, and remove its tag:
    - if some strict ancestor of $x$, a node other than $x$ on the path from the root to $x$, is labelled $M$, tag $x$ "old";
    - otherwise, if no transition is enabled at $M$, tag $x$ "dead-end";
    - otherwise, for each transition $t$ enabled at $M$, let $M'$ be the $\omega$-marking obtained by firing $t$ at $M$, and let $M'''$ agree with $M'$ except that $M'''(p) = \omega$ for every place $p$ such that some node on the path from the root to $x$, $x$ itself included, has a label $M''$ with $M'' \le M'$, $M'' \ne M'$ and $M''(p) < M'(p)$; every comparison is made with $M'$ itself, not with a partly accelerated label. Add a child of $x$ labelled $M'''$, with an arc labelled $t$, and tag it "new".

The *coverability graph* is obtained from the tree by identifying all nodes with equal labels: its nodes are the distinct labels of the tree, and it has an arc labelled $t$ from $M_1$ to $M_2$ whenever the tree has an arc labelled $t$ from a node labelled $M_1$ to a node labelled $M_2$. For a bounded net no label contains $\omega$, and the tree and graph are the reachability tree and the [reachability graph](../reachability-set-and-reachability-graph.md).

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [Boundedness and safeness of Petri nets](../boundedness-and-safeness.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section V-A ("The coverability tree"): the symbol $\omega$, Steps 1–2.4.3 of the construction, and the coverability graph of Fig. 18(b), obtained by merging the nodes of the tree in Fig. 18(a) that have the same label. Murata's Step 2.2 compares $M$ with "a marking on the path from the root to $M$"; that path contains the node itself, so the comparison is taken here with strict ancestors, while the acceleration in Step 2.4.2 compares the firing result with every node on the path, the node being expanded included, once.
