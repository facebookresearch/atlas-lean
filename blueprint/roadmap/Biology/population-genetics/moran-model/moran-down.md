# Down-step probability of the Moran process

Probability that one step of the Moran process takes the mutant count from `i` to `i - 1`:
a wild type is chosen to reproduce (probability `(N - i) / (r i + N - i)`) and a mutant is
chosen to die (probability `i / N`). Meaningful for `0 < r` and `i ≤ N`.
