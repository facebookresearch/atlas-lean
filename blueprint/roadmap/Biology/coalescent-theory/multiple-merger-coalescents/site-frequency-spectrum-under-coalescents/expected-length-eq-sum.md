# The expected branch length is the whole occupation sum

For a nonzero finite measure `Λ` on `[0, 1]`, a natural number `i`, a list `b` of `|b|` block
sizes and every `N ≥ |b|`, the [expected length](expected-length.md) satisfies
`E L_i(b) = ∑_{j < N} E[h_i(X_j)]`, with the [holding count](holding-count.md) `h_i` and the
expectation after `j` jumps of the block-size jump chain `X` started at `b`: the jumps from the
`|b|`-th on add nothing. The identity holds for every list of natural numbers; the reading as
branch lengths of a genealogy needs positive block sizes.
