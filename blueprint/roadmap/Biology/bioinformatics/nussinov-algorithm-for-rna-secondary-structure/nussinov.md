# The Nussinov recursion

The first base `a` of `a :: rest` is either unpaired, or paired
with `rest[k]` for some `k ≥ m` with `pair a rest[k]`, splitting the rest into the enclosed part
`rest.take k` and the outer part `rest.drop (k + 1)`. Exponential-time specification; the usual
`O(n³)` table memoizes it on the intervals of `s`.
