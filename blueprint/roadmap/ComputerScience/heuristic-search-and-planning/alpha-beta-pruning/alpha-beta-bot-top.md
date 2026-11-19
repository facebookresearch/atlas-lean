# Alpha-beta with the full window returns the minimax value

Let $t$ be a game tree whose
values lie in a bounded linear order with least element $\bot$ and greatest element $\top$. For
either player $p$ to move, alpha-beta pruning run on $t$ for $p$ with the window $[\bot, \top]$
returns exactly the minimax value of $t$ for $p$.
