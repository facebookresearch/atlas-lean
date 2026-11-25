# Transition operator of the block-size jump chain

For a finite measure `Λ` on `[0, 1]`, the transition operator of the block-size jump chain of
the Λ-coalescent sends a statistic `g` of block-size lists to the function whose value at a list
`b` of `|b|` blocks is `∑_K (λ_{|b|,|K|} / λ_{|b|}) g(b_K)`, the sum running over all sets `K` of
positions of `b`, where `b_K` is the list with the [blocks at `K` merged](merge-set.md),
`λ_{|b|,|K|}` is the [merger rate](../../coalescents/merger-rate.md) (`0` unless `|K| ≥ 2`) and
`λ_{|b|}` the [total merger rate](../../coalescents/total-merger-rate.md). When `λ_{|b|} = 0`
(fewer than two blocks, or `Λ = 0`) the value is `g(b)`: such a state is absorbing, and no
quotient by `λ_{|b|}` is formed. The operator is defined on all lists of natural numbers; the
configurations of a genealogy are the lists of positive block sizes.
