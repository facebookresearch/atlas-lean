# Sequent-peak storage deficit after t steps

For required releases `R` and inflows `Q` over `n` time steps, with deficits `dᵢ = Rᵢ - Qᵢ`, the
storage deficit `K_t` after the first `t` steps is the Lindley reflected walk of `d₀, …, d_{t-1}`:
`K₀ = 0` and `K_{k+1} = max 0 (K_k + d_k)`. It is the sequent-peak drawdown below a full reservoir
that spills excess inflow. It is defined for every natural `t`: for `t ≥ n` only the `n` recorded
deficits enter, so the value is the deficit `K_n` at the end of the horizon; the intended range is
`t ≤ n`. There it is the largest net deficit `d_i + … + d_{t-1}` over a final window of steps
`i ≤ k < t` with `0 ≤ i ≤ t`, the empty window counting as `0`
([bound](suffix-deficit-sum-le-required-storage-a.md),
[attainment](exists-suffix-deficit-sum-eq-required-st.md)). The storage capacity that meets the
release over the whole horizon is the [worst required storage](worst-required-storage.md), not
this value.
