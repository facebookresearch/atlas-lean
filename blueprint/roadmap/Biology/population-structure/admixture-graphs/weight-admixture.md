# Lineage weight recursion at an admixture node

In an [admixture graph](admixture-graph.md), let $X$ be a node with $\mathrm{pa}(X) = \{A, B\}$, $A \ne B$, and put $\alpha = a(X, A)$. Then for every [edge](edge.md) $e = (c, p)$,

$$w(X, e) = \alpha\, w(A, e) + (1 - \alpha)\, w(B, e) + \begin{cases} a(X, p) & c = X,\\ 0 & c \ne X, \end{cases}$$

where $w$ is the [lineage weight](weight.md); the last term is $\alpha$ on the edge $(X, A)$, $1 - \alpha$ on $(X, B)$ and $0$ elsewhere.
