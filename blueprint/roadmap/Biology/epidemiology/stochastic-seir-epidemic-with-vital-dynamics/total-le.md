# The population grows only by births

Let `β`, `σ`, `γ`, `μ` be real and let `(S, E, I, R)` be a [chain path](is-chain-path.md) at scale
`N` driven by the functions `y_c`. Then at every `t ≥ 0`

`S(t) + E(t) + I(t) + R(t) ≤ S(0) + E(0) + I(0) + R(0) + y_birth(A_birth(t))`,

where `A_birth(t) = max(N μ t, 0)` is the [birth clock](clock-birth.md), equal to `N μ t` for
`μ ≥ 0`. Infections, progressions and recoveries move individuals between compartments, and the
death counts are natural numbers.
