# Row vector times the oriented incidence matrix

Let $V$ be a finite set, $E$ a set, and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$, with [oriented incidence matrix](oriented-incidence.md) $B$. For every $x : V \to \mathbb{R}$ and $e \in E$, the entry $e$ of the row vector $x^{\mathsf T} B$ is the difference $x(e^-) - x(e^+)$ across $e$.
