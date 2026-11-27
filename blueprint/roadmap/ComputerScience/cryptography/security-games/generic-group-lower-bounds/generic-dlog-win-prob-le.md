# Generic discrete-logarithm bound, uniform encoding

Let `q` be prime and let `A` be a
decision tree that is given the labels of `0`, `1` and the secret `x`, tests labels only for
equality, and makes at most `m` group operations on every path (`GTree.numQueries A ≤ m`). For a
uniform encoding (a permutation of `ZMod q`) and a uniform secret `x`, `A` outputs `x` with
probability at most `((m + 3).choose 2 + 1) / q` (`genericDlogGame`).

## Sources

- V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of the Eurocrypt 1997 paper, Section 2, Theorem 1, here for prime order in Nechaev's model.
