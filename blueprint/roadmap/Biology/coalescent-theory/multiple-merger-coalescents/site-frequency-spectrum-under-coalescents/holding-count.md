# Branch length subtending i copies accumulated in one state

For a finite measure `Λ` on `[0, 1]`, a natural number `i` and a list `b` of `|b|` block sizes,
the holding count is `#{blocks of size i in b} / λ_{|b|}`, the number of blocks of size `i` times
the mean holding time `1 / λ_{|b|}` of `b`, where `λ_{|b|}` is the
[total merger rate](../../coalescents/total-merger-rate.md): the expected length, accumulated
while the chain sits in `b`, of branches subtending `i` copies. With the convention `x / 0 = 0`
it is `0` when `λ_{|b|} = 0` (fewer than two blocks, or `Λ = 0`).
