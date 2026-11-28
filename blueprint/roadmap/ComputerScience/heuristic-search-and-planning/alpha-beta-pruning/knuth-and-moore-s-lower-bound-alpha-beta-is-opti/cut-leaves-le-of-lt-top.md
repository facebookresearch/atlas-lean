# The minimizer's strategy

Let $s$ be a game tree of uniform shape with branching factor $k$ and depth $d$ whose leaves carry variables, $Q$ a finite set of variables, and $hi$ a valuation of the variables with $hi(i) = \top$ for $i \notin Q$. If the minimax value of $s$ under $hi$ is below $\top$, then at least $k^{\lfloor d/2 \rfloor}$ leaves of $s$ carry a variable in $Q$ when the minimizer moves at the root, and at least $k^{\lceil d/2 \rceil}$ when the maximizer does.
