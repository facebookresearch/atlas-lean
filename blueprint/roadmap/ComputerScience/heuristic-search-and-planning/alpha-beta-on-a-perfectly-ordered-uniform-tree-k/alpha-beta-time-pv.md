# Principal node

Let $t$ be a game tree that is uniform of branching factor $k$ and depth $d$, let either player be to move, and let $t$ be perfectly ordered for that player. If the minimax value $v$ of $t$ lies strictly inside the window, $a < v < b$, then alpha-beta search with window $(a, b)$ evaluates exactly $k^{\lceil d/2 \rceil} + k^{\lfloor d/2 \rfloor} - 1$ leaves of $t$.
