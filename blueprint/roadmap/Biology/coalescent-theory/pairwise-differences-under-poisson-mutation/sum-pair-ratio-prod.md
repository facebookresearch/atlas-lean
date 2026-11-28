# Mixing hypoexponential transforms over the epoch of coalescence

Let `N ≥ 2`, let `r_m = (m - 1) / (m + 1)` be the [ratio](pair-ratio.md), and let `z` be a
complex number with `z ≠ C(k, 2)` for every `k ≥ 2`, that is, `z ∉ {1, 3, 6, 10, …}`. Then

`∑_{m=2}^N (r_m - r_{m-1}) ∏_{k=m}^N C(k, 2) / (C(k, 2) - z) = r_N / (1 - z)`.

For `z = i u` with `u` real, the product is the characteristic function at `u` of the
hypoexponential sum `T_m + ⋯ + T_N` of independent `T_k` with the exponential law of rate
`C(k, 2)`, and `1 / (1 - i u)` is that of the exponential law with rate `1`. So mixing these sums
over the epoch `m` in which a pair coalesces, with the weights `r_m - r_{m-1}`, which sum to
`r_N`, gives `r_N` times the characteristic function of `Exp(1)`.
