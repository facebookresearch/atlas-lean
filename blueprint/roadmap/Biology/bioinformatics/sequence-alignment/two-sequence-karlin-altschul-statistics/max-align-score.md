# Max Align Score

The **maximal ungapped alignment score** of `u` and `v`: the largest `alignScore` over all
start positions `i ≤ |u|`, `j ≤ |v|` and length bounds `ℓ ≤ |u|` (the empty alignment scores
`0`). Every alignment of a window of `u` with a window of `v` of the same length occurs, and every
triple scores such an alignment (`alignScore_eq_min`), so this is the best ungapped alignment
score.
