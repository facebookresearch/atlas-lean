# The decoded list of an accepted encoding is the powers of 9/10

For every list of characters `s` accepted by the [encoded-trace checker](check-encoded-trace.md),
`s` [decodes](decode-trace.md) to a list `y` with eleven entries and `y_j = (9/10)^j` in the reals
for `j = 0, …, 10`; these are the coefficients of `T_j = T_amb + Δ y_j` for every `Δ`, including
`Δ = 0`.
