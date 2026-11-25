# Splitting compositions along a sub-multiset of their parts

For functions `H` and `K` from finite multisets of natural numbers to the reals and natural numbers
`k`, `N` and `m`,

`∑_c ∑_s H(s) K(P(c) - s) = C(k, m) ∑_{x=0}^{N} (∑_u H(P(u))) (∑_v K(P(v)))`,

where `c` runs over the compositions of `N` into `k` positive parts (ordered `k`-tuples of positive
integers with sum `N`), `P(c)` is the multiset of the parts of `c`, `s` runs over the `C(k, m)`
sub-multisets of `P(c)` with `m` elements (one for each set of `m` positions), `P(c) - s` is the
complementary sub-multiset, `u` runs over the compositions of `x` into `m` positive parts and `v`
over the compositions of `N - x` into `k - m` positive parts. When `m > k` both sides are `0`: no
such `s` exists and `C(k, m) = 0`.
