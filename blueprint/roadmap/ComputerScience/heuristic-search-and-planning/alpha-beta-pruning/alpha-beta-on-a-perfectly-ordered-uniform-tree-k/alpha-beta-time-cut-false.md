# Cut node of the minimizer

For a perfectly ordered uniform game tree of branching factor `k` and depth `d` with the minimizer to move, if `a < b` and the minimax value is at most `a`, alpha-beta search with window `(a, b)` evaluates exactly $k^{\lfloor d/2 \rfloor}$ leaves.
