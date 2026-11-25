# Lineage weight recursion at a tree node

In an [admixture graph](admixture-graph.md), let $X$ be a node with the single parent $Y$. Then for every [edge](edge.md) $e = (c, p)$,

$$w(X, e) = w(Y, e) + \begin{cases} 1 & c = X,\\ 0 & c \ne X, \end{cases}$$

where $w$ is the [lineage weight](weight.md).
