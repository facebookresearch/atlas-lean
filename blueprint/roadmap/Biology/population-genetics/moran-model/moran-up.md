# Up-step probability of the Moran process

Probability that one step of the Moran process with `N` individuals and mutant relative
fitness `r` takes the mutant count from `i` to `i + 1`: a mutant is chosen to reproduce
(probability `r i / (r i + N - i)`) and a wild type is chosen to die (probability
`(N - i) / N`). Meaningful for `0 < r` and `i ≤ N` (the real subtraction `N - i` is negative
for `i > N`).
