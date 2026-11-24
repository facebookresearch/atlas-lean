# Message delivery under a crash pattern

Let $\pi$ be a [crash pattern](crash-pattern.md), $r$ a round and $j$, $i$ processes. The message of $j$ to $i$ in round $r$ is delivered under $\pi$ always if $j$ is correct, and, if $j$ crashes in round $\rho$ with recipients $D$, exactly when $r < \rho$, or $r = \rho$ and $i \in D$.
