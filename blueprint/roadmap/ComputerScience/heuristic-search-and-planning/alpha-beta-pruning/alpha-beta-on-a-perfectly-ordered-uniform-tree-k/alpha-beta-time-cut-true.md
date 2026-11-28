# Cut node of the maximizer

For a perfectly ordered uniform game tree of branching factor `k` and depth `d` with the maximizer to move, if `a < b` and the minimax value is at least `b`, alpha-beta search with window `(a, b)` evaluates exactly $k^{\lfloor d/2 \rfloor}$ leaves.
