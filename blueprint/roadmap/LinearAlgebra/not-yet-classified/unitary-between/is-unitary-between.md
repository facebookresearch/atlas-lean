# Is Unitary Between

A rectangular matrix `U : Matrix out inp R` is unitary between `inp` and `out`
when `Uᴴ * U = 1` on `inp` and `U * Uᴴ = 1` on `out`, where `Uᴴ = Matrix.conjTranspose U`.

Orientation: `out` is the row/output index, `inp` is the column/input index,
so `U : Matrix out inp R` is a linear map `inp → out`. Both equalities are
required; this represents a unitary isomorphism between possibly differently
named finite bases, not an isometry-only condition.
