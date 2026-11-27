# Risk-neutral default probability from state prices

For state prices `ψ(ω)` on a finite state space and a set of default states, the risk-neutral
default probability is `q_D = (∑_{ω default} ψ(ω)) / D`, the state-price mass of the default
states divided by the risk-free discount factor `D = ∑_ω ψ(ω)`; with the convention
`x / 0 = 0`, `q_D = 0` when `D = 0`. When there is at least one state and every state price is
positive, the weights `ψ(ω) / D` are positive and sum to `1`, and `q_D` is the total weight
they give the default states, so `q_D` is a risk-neutral probability of default; for arbitrary
`ψ` it is only a ratio.
