# First-step decomposition of the expected branch lengths

For a nonzero finite measure `Λ` on `[0, 1]`, a natural number `i` and a list `b` of `|b| ≥ 2`
block sizes, the [expected length](expected-length.md) of branches subtending `i` copies is
`E L_i(b) = #{blocks of size i in b} / λ_{|b|} + ∑_K (λ_{|b|,|K|} / λ_{|b|}) E L_i(b_K)`, the sum
running over all sets `K` of positions of `b`, with `b_K` the list with the
[blocks at `K` merged](merge-set.md): the length accumulated in `b` plus the average, over the
first merger `K`, of the expected length after it. The identity holds for every list of at least
two natural numbers, including zero entries, and every `i`; the reading as branch lengths of a
genealogy needs positive block sizes.
Its block-count counterpart is the first-jump recursion (8) of Birkner, Blath & Eldon (2013).
