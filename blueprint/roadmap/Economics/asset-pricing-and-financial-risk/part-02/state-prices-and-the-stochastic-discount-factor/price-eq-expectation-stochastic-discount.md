# State-price value equals SDF pricing

On a finite state space with physical weights `P(ω) > 0` for every state, the state-price value
`∑_ω ψ(ω) X(ω)` of a payoff `X` equals its `P`-weighted expectation under the induced stochastic
discount factor `m(ω) = ψ(ω) / P(ω)`: `∑_ω ψ(ω) X(ω) = ∑_ω P(ω) m(ω) X(ω)`. When
`∑_ω P(ω) = 1` the right-hand side is the physical expectation `E_P[m X]`; the identity does not
use the normalization.
