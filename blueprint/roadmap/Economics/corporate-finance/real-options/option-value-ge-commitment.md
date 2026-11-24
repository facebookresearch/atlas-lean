# An optional action beats committing to any one feasible action

Take a finite nonempty set of feasible actions, a finite set of states `Ω` with nonnegative
weights `p(ω) ≥ 0` (they need not sum to `1`) and payoffs `V(a, ω)`. For every feasible action
`b`, the expected value of committing to `b`, `∑_{ω ∈ Ω} p(ω) * V(b, ω)`, is at most the option
value `∑_{ω ∈ Ω} p(ω) * max_a V(a, ω)` of choosing the best action after seeing the state.
