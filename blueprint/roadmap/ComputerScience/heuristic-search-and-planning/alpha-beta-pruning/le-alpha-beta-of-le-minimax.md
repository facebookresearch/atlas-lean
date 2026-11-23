# Alpha-beta at or above the top of the window

Let values lie in a bounded linear order, let
$t$ be a game tree, let $p$ be a player, and let $a < b$. If the minimax value of $t$ with $p$ to
move is at least $b$, then the value returned by alpha-beta pruning on $t$ with $p$ to move and
window $[a, b]$ is at least $b$.
