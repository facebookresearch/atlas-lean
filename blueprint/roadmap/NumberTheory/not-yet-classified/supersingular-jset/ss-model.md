# Ss Model

The short Weierstrass curve `y ^ 2 = x ^ 3 + ssModelA p j * x + ssModelB p j` over the prime
field `ZMod p` attached to `j : ZMod p`. For `p > 3` it is an elliptic curve with `j`-invariant `j`
(`ssModel_j`). It is not a model in characteristic `2` or `3`, where its discriminant vanishes
for every `j`: in characteristic `2` the discriminant of every short Weierstrass equation does,
and in characteristic `3` the coefficient `ssModelA 3 j` is `0`. In every characteristic,
`WeierstrassCurve.ofJ j` is an elliptic curve with `j`-invariant `j`. The hypothesis
`[Fact p.Prime]` makes `ZMod p` the field with `p` elements (`ZMod (p ^ n)` is not a field for
`n > 1`).
