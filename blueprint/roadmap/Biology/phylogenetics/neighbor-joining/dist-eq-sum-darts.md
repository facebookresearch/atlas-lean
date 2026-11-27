# Split decomposition of a tree metric

Let $G$ be a finite tree, $\iota$ a map from a finite set $X$ to its vertices, $w$ real edge lengths, and $d$ such that $d(x, y)$ is the total length of every path from $\iota(x)$ to $\iota(y)$. Then for all taxa $x, y$,

$$d(x, y) = \frac12 \sum_{(p, v)} w(pv)\, [\,(p, v) \text{ separates } x, y\,],$$

the sum running over the darts $(p, v)$ of $G$, where $(p, v)$ separates $x, y$ if exactly one of them lies on the [$p$-side](side.md) of $\{p, v\}$.
