# Positive definite covariance gives a unique long-only optimum

Let `S` be a positive definite real matrix indexed by finitely many assets, `μ_i` their expected
returns and `m` a target return. If the long-only target-return slice (weight vectors `w` with
`w_i ≥ 0` for every `i`, `∑_i w_i = 1` and `∑_i μ_i w_i = m`) is nonempty, then exactly one
weight vector of the slice minimizes `wᵀ S w` on it: two distinct minimizers would make their
midpoint, which also lies in the slice, strictly better.
