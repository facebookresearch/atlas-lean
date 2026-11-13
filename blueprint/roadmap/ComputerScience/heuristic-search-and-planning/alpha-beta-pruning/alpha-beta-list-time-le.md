# Cost of the alpha-beta scan

For either player $p$, all values $a, b$ in a linear order
and every list $ts$ of game trees, the alpha-beta scan of $ts$ for $p$ with lower bound $a$ and
upper bound $b$ evaluates at most as many leaves as the trees in $ts$ have in total, each leaf
evaluation costing one unit.
