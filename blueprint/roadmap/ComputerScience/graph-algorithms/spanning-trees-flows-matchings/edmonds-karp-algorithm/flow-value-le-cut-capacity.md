# Weak max-flow min-cut duality

Let $c$ be a capacity function, $s$ and $t$ vertices, and
$f$ a flow that is feasible for $c$, $s$ and $t$. For every set $S$ of vertices with $s \in S$
and $t \notin S$, the net flow leaving $s$ under $f$ is at most the capacity of the cut $S$,
namely $\sum_{u \in S} \sum_{v \notin S} c(u, v)$.
