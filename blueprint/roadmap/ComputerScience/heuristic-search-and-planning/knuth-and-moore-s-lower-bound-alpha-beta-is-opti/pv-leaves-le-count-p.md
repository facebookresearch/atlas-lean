# Principal nodes

Let $s$ be a game tree of uniform shape with branching factor $k$ and depth $d$ whose leaves carry variables, $Q$ a finite set of variables, and $lo \le hi$ valuations of the variables with $lo(i) = \bot$ and $hi(i) = \top$ for $i \notin Q$. If, with player $p$ to move, $s$ has the same minimax value $v$ under $lo$ and under $hi$, and $\bot < v < \top$, then at least $k^{\lceil d/2 \rceil} + k^{\lfloor d/2 \rfloor} - 1$ leaves of $s$ carry a variable in $Q$ (subtraction truncated at $0$).
