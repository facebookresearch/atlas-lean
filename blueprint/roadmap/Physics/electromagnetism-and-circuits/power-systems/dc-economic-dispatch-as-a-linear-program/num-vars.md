# Number of variables of the dispatch linear program

For `n_N` buses and `n_G` generators, the dispatch linear program has `2 (n_G + n_N)` variables: a
first and a second nonnegative coordinate block, each with one entry for each of the `n_G + n_N`
free variables `(p, θ)`.
