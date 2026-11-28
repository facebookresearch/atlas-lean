# Risk-neutral default probability lies between 0 and 1

On a finite state space with strictly positive state prices `ψ(ω) > 0`, for any set of default
states, the risk-neutral default probability `q_D = (∑_{ω default} ψ(ω)) / ∑_ω ψ(ω)` satisfies
`0 ≤ q_D ≤ 1`. This is only a bound on a number: the state space may be empty, in which case
`q_D = 0` by the convention `x / 0 = 0`; reading `q_D` as a probability needs at least one
state.
