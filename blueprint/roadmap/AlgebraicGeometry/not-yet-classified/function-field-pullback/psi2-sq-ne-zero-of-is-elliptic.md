# `Ψ₂Sq` is nonzero on an elliptic curve

The polynomial `Ψ₂Sq`, whose roots are the
`x`-coordinates of the points of order two, is nonzero for an elliptic curve over a field. Mathlib's
`WeierstrassCurve.Ψ₂Sq_ne_zero` assumes `(4 : R) ≠ 0` instead; this version uses ellipticity, so it
also covers characteristic two.
