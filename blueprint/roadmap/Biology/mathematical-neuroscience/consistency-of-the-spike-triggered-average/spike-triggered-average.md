# Spike-triggered average

The response-weighted average
`(∑_{i<N} y_i)⁻¹ ∑_{i<N} y_i x_i` of the first `N` stimuli. It is `0` when
`∑_{i<N} y_i = 0` (for nonnegative responses, when none of the first `N` pairs has a spike), by
the convention `0⁻¹ = 0`.
