# Rank Desc

The **supremal `k`-th largest value** (counted with multiplicity, from `k = 0`) of a
sequence: the supremum over `(k + 1)`-element index sets `s` of `min_{i ∈ s} p i`. This is
in general a supremum, not an entry of `p` (e.g. `p n = 1 - 1 / (n + 1)` gives
`rankDesc p 0 = 1`, attained by no entry). For a nonnegative sequence tending to `0` the
supremum is attained and this is the `k`-th entry of the decreasing rearrangement, padded
with zeros when fewer than `k + 1` entries are positive.
