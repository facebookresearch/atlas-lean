# Alpha-beta fails low when the minimax value is at most the lower bound

Let $t$ be a game
tree with values in a bounded linear order, $p$ the player to move and $a < b$ values. If the
minimax value of $t$ for $p$ is at most $a$, then alpha-beta pruning run on $t$ for $p$ with the
window $[a, b]$ returns a value at most $a$.
