# Back-door adjustment for a set of predecessors containing the parents

Let `Z` be a set
of nodes preceding `k` in the topological order (so `Z` contains no descendant of `k`) that
contains the parents of `k`. Then `Z` meets the back-door criterion for every outcome node
`y ∉ Z` (a path from `k` to `y` that starts with an arrow into `k` starts `k ← p` with
`p ∈ pa(k) ⊆ Z`, an interior non-collider, so it is blocked), and for every function `f` of the
variables
`E[f | do(X_k = a)] = ∑_z P(Z = z) E[f | X_k = a, Z = z]`, assuming `P(X_k = a, Z = z) > 0`
whenever `P(Z = z) > 0` (Pearl 2009, Theorem 3.3.2, in this case).
