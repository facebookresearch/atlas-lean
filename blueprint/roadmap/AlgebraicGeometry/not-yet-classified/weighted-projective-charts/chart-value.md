# Chart Value

The fixed formula for an integer-character polynomial in a chart:
`Σ_a c_a x^a x_i^((t-weight(a))/w_i)`. When `k` has `w_i` distinct `w_i`-th roots of unity
(for instance `k` algebraically closed of characteristic zero, as in the Wanted chart
comparison), every monomial of a character-`t` polynomial has `t - weight(a)` divisible by
`w_i`, so the integer division is exact there. Over other fields `ℤ` division truncates.
