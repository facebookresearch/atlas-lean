# Shrinkage weight

For real numbers `b` and `s`, the shrinkage weight is `w = s / (b + s)`, with the convention
`x / 0 = 0` when `b + s = 0`. For `b > 0` and `s > 0` it is the weight of the per-cell estimate
`k / s` in the [posterior mean](posterior-mean-eq-shrinkage.md), the prior mean `a / b` getting the
weight `1 − w = b / (b + s)`; it depends only on the prior rate `b` and the size factor `s`.
