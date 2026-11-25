# Queue length at a fixed-time signal over one cycle

For an arrival rate `λ`, a service rate `μ`, a red duration `R` and a time `t` (real numbers), the
deterministic fluid queue at the signal is `Q(t) = λ t` for `t ≤ R` and
`Q(t) = max(0, λ R - (μ - λ)(t - R))` for `t > R`. The formula is defined for all real inputs; it is
meant for the regime `0 < λ < μ`, `R ≥ 0`. For `0 < t < R` it
[grows at the rate `λ`](queue-len-has-deriv-at-red.md). For `0 < λ < μ` it
[drains at the rate `μ - λ`](queue-len-has-deriv-at-green.md) at the times `t` with
`R < t < R + λ R / (μ - λ)` that lie before the end `R + G` of a green phase of duration `G`, and
with also `R ≥ 0` it [is `0`](queue-len-eq-zero-of-clearance.md) from the clearance time
`R + λ R / (μ - λ)` on. The green duration and the cycle length are not parameters: times beyond the
cycle end belong to the next cycle of a periodic signal, which this one-cycle model does not
describe.
