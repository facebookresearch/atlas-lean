# Grid step path in the Skorokhod space

Fix a real $\tau$ and $K$ grid steps of length $\tau/K$. For increments $y \in \mathbb{R}^K$, the grid step path is the element $t \mapsto \sum_{i<K}y_i\mathbf 1\{(i+1)\tau/K \le t\}$ of $D([0, \tau])$: at $t$ it sums the increments whose right endpoints $(i+1)\tau/K$ are at or before $t$. For $\tau > 0$ it is the càdlàg pure-jump path that starts at $0$ and jumps by $y_i$ at $(i+1)\tau/K$; for $\tau = 0$ every right endpoint is $0$, so its value at $0$ is $\sum_{i<K}y_i$.
