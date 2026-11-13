# World

The **bootstrap world** built on the data `x`: a single probability space
`ℕ → ℕ → α` on which, for every sample size `n`, the row `ω n` is an iid sequence drawn from
the empirical distribution `empirical x n`, and different rows are independent. The bootstrap
resample at sample size `n` is `(ω n 0, …, ω n (n - 1))`. The measure depends only on the
data, so laws under `world x` are the *conditional* laws of bootstrap statistics given the
sample.
