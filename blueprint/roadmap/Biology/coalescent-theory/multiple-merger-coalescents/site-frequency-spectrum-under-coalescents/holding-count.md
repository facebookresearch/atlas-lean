# Branch length subtending i copies accumulated in one state

For a finite measure `Λ` on `[0, 1]`, a natural number `i` and a list `b` of `|b|` natural
numbers, the holding count is `h_i(b) = #{entries of b equal to i} / λ_{|b|}`, where `λ_{|b|}` is
the [total merger rate](../../coalescents/total-merger-rate.md). With the convention `x / 0 = 0`
it is `0` when `λ_{|b|} = 0` (fewer than two blocks, or `Λ = 0`). When `λ_{|b|} > 0` and `b` lists
positive block sizes (a configuration of the genealogy), `1 / λ_{|b|}` is the mean holding time
of `b`, and `h_i(b)` is the expected length, accumulated while the chain sits in `b`, of branches
subtending `i` sampled copies. When `λ_{|b|} = 0` this reading fails: the state is never left and
the time spent there is infinite, although the formula gives `0`. The formula also accepts lists
with zero entries, which are not blocks of a genealogy.
