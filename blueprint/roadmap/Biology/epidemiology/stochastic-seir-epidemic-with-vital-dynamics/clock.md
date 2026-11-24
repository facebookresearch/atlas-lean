# Internal clocks of the channels

For real parameters `β`, `σ`, `γ`, `μ`, a scale `N ∈ ℕ`, count paths `S, E, I, R : ℝ → ℕ`, a
[channel](channel.md) `c` and a time `t`, the internal clock of `c` is the nonnegative real

`A_c(t) = max(∫₀ᵗ rate_c(x) dx, 0)`,

the integrated [intensity](rate.md), truncated at `0` so that it can index a counting process on
`[0, ∞)`. The integral is oriented (for `t < 0` it is `-∫ₜ⁰ rate_c(x) dx`) and is `0` when the
intensity is not integrable between `0` and `t`. For nonnegative parameters the intensities are
nonnegative, so `A_c(t) = 0` for `t ≤ 0`.
