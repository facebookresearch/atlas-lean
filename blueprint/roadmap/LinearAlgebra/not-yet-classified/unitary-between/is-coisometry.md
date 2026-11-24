# Is Coisometry

A rectangular matrix `U : Matrix out inp R` is a coisometry when
`U * Uᴴ = 1` on the output/row index `out`, where `Uᴴ = Matrix.conjTranspose U`.

Orientation: `out` is the row/output index, `inp` is the column/input index.
The condition `U * Uᴴ = 1` requires `[Fintype inp]` and `[DecidableEq out]`.
Empty types are supported.
