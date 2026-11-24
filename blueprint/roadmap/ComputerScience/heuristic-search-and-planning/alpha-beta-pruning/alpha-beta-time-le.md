# Alpha-beta never evaluates more leaves than the tree has

For either player $p$ to move
and all values $a, b$ in a linear order, alpha-beta pruning run on a game tree $t$ for $p$ with
window $[a, b]$ evaluates at most as many leaves as $t$ has, each leaf evaluation costing one
unit.
