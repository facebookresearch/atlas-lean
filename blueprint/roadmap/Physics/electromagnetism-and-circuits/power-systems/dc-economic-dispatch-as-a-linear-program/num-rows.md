# Number of constraints of the dispatch linear program

For `n_N` buses, `n_E` branches and `n_G` generators, the dispatch linear program has
`2 n_N + 2 + 2 n_G + 2 n_E` inequality rows: two for each bus balance, two for the reference angle,
two for each generator limit pair and two for each branch-flow limit pair.
