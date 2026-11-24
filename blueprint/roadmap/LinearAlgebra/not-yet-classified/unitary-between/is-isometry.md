# Is Isometry

A rectangular matrix `U : Matrix out inp R` is an isometry when
`Uᴴ * U = 1` on the input/column index `inp`, where `Uᴴ = Matrix.conjTranspose U`.

Orientation: `out` is the row/output index, `inp` is the column/input index,
so `U : Matrix out inp R` represents a linear map `inp → out`. The condition
`Uᴴ * U = 1` requires `[Fintype out]` for the middle sum and `[DecidableEq inp]`
for the identity on `inp`. Empty types are supported.
