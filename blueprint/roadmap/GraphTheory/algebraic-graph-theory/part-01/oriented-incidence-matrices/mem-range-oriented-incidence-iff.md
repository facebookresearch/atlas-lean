# Range of the oriented incidence matrix

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with no loops, and let $B$ be its [oriented incidence matrix](oriented-incidence.md). A vector $r : V \to \mathbb{R}$ lies in the column space of $B$ (that is, $r = B\theta$ for some $\theta : E \to \mathbb{R}$) if and only if $\sum_{v \in C} r(v) = 0$ for every connected component $C$ of the [underlying graph](underlying-graph.md).
