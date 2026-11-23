# Three-population statistic at an admixture node

Let $G$ be an [admixture graph](admixture-graph.md) on a finite set of nodes, and let $M$ be a [drift model](../patterson-s-f-statistics/drift-model.md) on the edges of $G$ with drift lengths $\ell$ whose lineage weights are the [lineage weights](weight.md) of $G$. Let $X$ be a node with $\mathrm{pa}(X) = \{A, B\}$, $A \ne B$, and put $\alpha = a(X, A)$, $\beta = a(X, B)$ (so $\alpha + \beta = 1$). Then

$$f_3(X; A, B) = \alpha^2 \ell_{(X, A)} + \beta^2 \ell_{(X, B)} - \alpha \beta\, f_2(A, B),$$

where $f_2$ and $f_3$ are the [f2](../patterson-s-f-statistics/f2.md) and [f3](../patterson-s-f-statistics/f3.md) statistics of the population frequencies of $M$.
