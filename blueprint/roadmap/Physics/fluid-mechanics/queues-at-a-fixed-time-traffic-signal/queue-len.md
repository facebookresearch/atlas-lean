# Queue length at a fixed-time signal over one cycle

For an arrival rate `λ`, a service rate `μ`, a red duration `R` and a time `t` (real numbers), the
deterministic fluid queue at the signal is `Q(t) = λ t` for `t ≤ R` and
`Q(t) = max(0, λ R - (μ - λ)(t - R))` for `t > R`: it grows at the rate `λ` during red, then drains
at the rate `μ - λ` until it clears and stays at `0`. This reading is the regime `0 < λ < μ`,
`R ≥ 0`; the formula is defined for all real inputs. The green duration and the cycle length are not
parameters: times beyond the cycle end belong to the next cycle of a periodic signal, which this
one-cycle model does not describe.
