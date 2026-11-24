# First-step recursion for lineage weights

In every [admixture graph](admixture-graph.md), for every node $X$ and every [edge](edge.md) $e = (c, p)$,

$$w(X, e) = \sum_{Y \in \mathrm{pa}(X)} a(X, Y)\, w(Y, e) + \begin{cases} a(X, p) & c = X,\\ 0 & c \ne X, \end{cases}$$

where $w$ is the [lineage weight](weight.md): a lineage from $X$ traverses $e$ either as its first step or after moving to a parent $Y$, chosen with probability $a(X, Y)$.
