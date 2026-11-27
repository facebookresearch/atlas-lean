# Connection by an open path within a set

Let $d \in \mathbb{N}$, let $\omega$ be a bond configuration on $\mathbb{Z}^d$ and let $S \subseteq \mathbb{Z}^d$. Two sites $x, y \in S$ are connected by an open path within $S$, written $x \xleftrightarrow{S} y$, if they are reachable from each other in the [open subgraph induced on](open-subgraph-induce.md) $S$, that is, there is a path $x = z_0, z_1, \dots, z_k = y$ with all $z_i \in S$ and every edge $\{z_{i-1}, z_i\}$ open. The case $k = 0$ is allowed, so $x \xleftrightarrow{S} x$ for every $x \in S$.
