# Shrinkage Weight

The shrinkage weight `w = s / (b + s)` on the per-cell estimate `k / s`; the prior mean
`a / b` gets weight `1 - w = b / (b + s)`. It depends only on the prior rate `b` and the size
factor `s`.
