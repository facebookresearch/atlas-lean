# Choosing after seeing the state is worth at least the best commitment

Take a finite nonempty set of feasible actions, a finite set of states `Ω` with nonnegative
weights `p(ω) ≥ 0` (they need not sum to `1`) and payoffs `V(a, ω)`. The maximum over feasible
actions of the committed expected values, `max_a ∑_{ω ∈ Ω} p(ω) * V(a, ω)`, is at most the option
value `∑_{ω ∈ Ω} p(ω) * max_a V(a, ω)` of choosing the best action after seeing the state.
