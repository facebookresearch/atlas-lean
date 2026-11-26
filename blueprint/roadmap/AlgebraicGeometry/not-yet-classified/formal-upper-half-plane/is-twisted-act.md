# The Frobenius-twisted relation

For `g ∈ GL₂(K)`, the relation that holds between pairs
`x` and `x'` when the algebra map `x'.1` is `x.1` twisted by `frobTwist` with exponent `-vdet g`
and the Deligne datum `x'.2` is the pullback of `x.2` along `g⁻¹` (`DeligneDatum.IsPullback`).
The automorphism `Fr` of `Onr` and the homomorphism `vdet : GL₂(K) →* Multiplicative ℤ` are
arbitrary inputs.
