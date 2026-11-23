# Expected length of branches subtending i sample copies

For a finite measure `Λ` on `[0, 1]`, a natural number `i` and a list `b` of `|b|` block sizes,
the expected total length of branches subtending exactly `i` sample copies, for the Λ-coalescent
started from the block sizes `b`, is `E L_i(b) = ∑_{j < |b|} E[h_i(X_j)]`, where `X` is the
block-size jump chain started at `b`, the expectation after `j` jumps is given by the `j`-th
power of the [transition operator](jump-step.md), and `h_i` is the
[holding count](holding-count.md). For `Λ ≠ 0` the jumps from the `|b|`-th on contribute nothing,
so this is the [whole occupation sum](expected-length-eq-sum.md). For `Λ = 0` nothing ever
merges, so from a list of at least two blocks one of which has size `i` the true length is
infinite; the definition returns `0`, since every holding count is then `0` by the convention
`x / 0 = 0`.
