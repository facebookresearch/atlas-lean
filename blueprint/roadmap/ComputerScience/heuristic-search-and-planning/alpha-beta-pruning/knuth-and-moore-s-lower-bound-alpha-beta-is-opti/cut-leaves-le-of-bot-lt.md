# The maximizer's strategy

Let $s$ be a game tree of uniform shape with branching factor $k$ and depth $d$ whose leaves carry variables, $Q$ a finite set of variables, and $lo$ a valuation of the variables with $lo(i) = \bot$ for $i \notin Q$. If the minimax value of $s$ under $lo$ is above $\bot$, then at least $k^{\lfloor d/2 \rfloor}$ leaves of $s$ carry a variable in $Q$ when the maximizer moves at the root, and at least $k^{\lceil d/2 \rceil}$ when the minimizer does.
