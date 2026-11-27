# Baby-step giant-step decomposition of an exponent

Let `1 < q`, `0 < m` and `q ≤ m ^ 2`. For every `x : ZMod q`, the quotient
`x.val / m` and the remainder `x.val % m` are both less than `m`, and `x -
(x.val / m) * m = x.val % m` in `ZMod q`.
