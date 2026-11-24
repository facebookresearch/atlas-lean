# Posterior mean at a zero count

For real `a`, `b > 0` and `s > 0`, the [posterior mean](posterior-mean.md) at the count `k = 0` is
`a / (b + s) = (1 − w) · (a / b)` with the [shrinkage weight](shrinkage-weight.md)
`w = s / (b + s)`: the per-cell estimate is `0` and the posterior mean is the shrunk prior mean.
