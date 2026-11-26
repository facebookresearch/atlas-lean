# Ss JSet

The supersingular `j`-invariants in characteristic `p`, for a prime `p`: the `j` in an
algebraic closure of `ZMod p` such that every elliptic curve over that algebraic closure with
`j`-invariant `j` is supersingular in the sense of `WeierstrassCurve.Affine.IsSupersingular`, that
is, has no nonzero geometric point killed by `p`. Every `j` is the `j`-invariant of an elliptic
curve, for example `WeierstrassCurve.ofJ j`, so the condition is not vacuous.
