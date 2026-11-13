# States reachable by UPGMA

The states reachable by **UPGMA** (Sokal & Michener 1958) on `d`: a partition `P` of the
taxa into blocks and the heights `c x y` recorded so far. It starts from the singletons; each
step merges two distinct blocks `C`, `D` of least average linkage (ties broken arbitrarily) and
records `avgDist d C D` as the height at which every `x ∈ C` and `y ∈ D` are joined (the
distance between them in the output tree; their common ancestor sits at half of it).
