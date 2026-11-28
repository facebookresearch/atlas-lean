# Lipschitz bound for the scaled intensities

Let `β`, `σ`, `γ`, `μ` be nonnegative, and let `K`, `M`, `(s, e, i, r)` and `(s', e', i', r')` be
real with `0 ≤ s ≤ K` and `|i'| ≤ M`. Then for every [channel](channel.md) `c` the
[scaled intensities](scaled-rate.md) satisfy

`|λ_c(s, e, i, r) - λ_c(s', e', i', r')| ≤ (β (K + M) + σ + γ + μ) D`,

where `D = |s - s'| + |e - e'| + |i - i'| + |r - r'|` is the `ℓ¹` distance. Only the infection term
`β s i` is nonlinear; it needs the two bounds.
