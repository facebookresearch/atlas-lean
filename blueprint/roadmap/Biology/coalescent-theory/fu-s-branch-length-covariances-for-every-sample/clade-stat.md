# Clade statistic of a multiset of block sizes

For a natural number `k`, a function `φ` from the natural numbers to the reals and a finite
multiset `B` of natural numbers (block sizes), the clade statistic is

`S_k(φ, B) = ∑_s w_k(|s|) φ(Σ s)`,

where `s` runs over the `2^|B|` sub-multisets of `B`, one for each set of positions (a repeated
size gives repeated sub-multisets), `|s|` is the number of elements of `s` and `Σ s` their sum, and
`w_k(m) = 2 / (m C(k, m))` for `1 ≤ m < k` and `0` otherwise is the [clade weight](clade-weight.md).
It is defined for every `k`; in use, `B` has `k` elements.
