# Enumeration of the relaxation constraints

For `n_N` buses and `n_E` branches, the constraints indexed by a pair (one of six groups, bus) or by
a branch are put in bijection with `{0, …, 6 n_N + n_E - 1}`: the pair (group `g`, bus `k`), with
`g ∈ {0, …, 5}` and `k ∈ {0, …, n_N - 1}`, goes to `g n_N + k`, and branch `e` to `6 n_N + e`.
