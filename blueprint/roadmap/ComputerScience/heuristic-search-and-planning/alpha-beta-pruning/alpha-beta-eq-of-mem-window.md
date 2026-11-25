# Alpha-beta is exact inside the window

Let $t$ be a game tree with values in a bounded
linear order, $p$ the player to move and $a, b$ values. If the minimax value $v$ of $t$ for $p$
satisfies $a < v < b$, then alpha-beta pruning run on $t$ for $p$ with the window $[a, b]$ returns
exactly $v$.
