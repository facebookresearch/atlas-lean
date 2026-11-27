# Expected length of branches subtending i sample copies

For a finite measure `Λ` on `[0, 1]`, a natural number `i` and a list `b` of `|b|` natural numbers,
the expected length is `E L_i(b) = ∑_{j < |b|} E[h_i(X_j)]`, where `X` is the block-size jump chain
started at `b`, the expectation after `j` jumps is given by the `j`-th power of the
[transition operator](jump-step.md), and `h_i` is the [holding count](holding-count.md). The formula
is defined for every list of natural numbers, including lists with zero entries, which are not
configurations of a genealogy. When `Λ ≠ 0`, `b` lists positive block sizes and `i ≥ 1`, it is the
expected total length of branches subtending exactly `i` sample copies for the Λ-coalescent started
from the block sizes `b`; for `Λ ≠ 0` the jumps from the `|b|`-th on contribute nothing, so this is
the [whole occupation sum](expected-length-eq-sum.md). For `Λ = 0` nothing ever merges, so from a
list of at least two blocks one of which has size `i` the true length is infinite, while the
definition returns `0`: every holding count is then `c / 0 = 0` by the convention `x / 0 = 0`,
where `c` is the number of entries equal to `i`, even when `c > 0`. This value `0` is not an
expected length.
