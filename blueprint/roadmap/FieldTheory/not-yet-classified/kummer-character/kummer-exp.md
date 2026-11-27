# Kummer exponent

Let `p` be a prime and `ζ` a primitive `p`-th
root of unity in `AlgebraicClosure ℚ`. For every intermediate field `F`
of `AlgebraicClosure ℚ / ℚ`, a unit `x` of `F` and `σ` in the fixing
subgroup of `F`, the Kummer exponent is the element `i` of `ZMod p` with
`σ (kummerRoot p F x) = ζ ^ i * kummerRoot p F x`. It is additive in `σ`
when also `ζ ∈ F` (see `kummerChar`); for general `F` it satisfies only
the twisted law `kummerExp_mul`.
