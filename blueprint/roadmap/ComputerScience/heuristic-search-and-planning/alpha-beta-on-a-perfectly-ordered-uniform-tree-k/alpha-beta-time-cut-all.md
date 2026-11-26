# Alpha-beta cost at cut and all nodes

Let $t$ be a uniform game tree of branching factor $k$ and depth $d$, and let $a < b$. With the
maximizer to move, if $t$ is perfectly ordered for the maximizer and its minimax value is at most
$a$, alpha-beta with window $(a, b)$ evaluates exactly $k^{\lceil d/2 \rceil}$ leaves (an all
node), and if its value is at least $b$ it evaluates exactly $k^{\lfloor d/2 \rfloor}$ leaves
(a cut node). Symmetrically, with the minimizer to move and $t$ perfectly ordered for the
minimizer, a value at least $b$ gives $k^{\lceil d/2 \rceil}$ leaves and a value at most $a$ gives
$k^{\lfloor d/2 \rfloor}$ leaves.
