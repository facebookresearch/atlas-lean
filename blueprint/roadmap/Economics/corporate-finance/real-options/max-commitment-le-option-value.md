# Choosing after seeing the state is worth at least the best commitment

Take a finite nonempty set of feasible actions, a finite set of states `Ω` with nonnegative
weights `p(ω) ≥ 0` (they need not sum to `1`) and payoffs `V(a, ω)`. The maximum over feasible
actions of the committed expected values, `max_a ∑_{ω ∈ Ω} p(ω) * V(a, ω)`, is at most the option
value `∑_{ω ∈ Ω} p(ω) * max_a V(a, ω)` of choosing the best action after seeing the state.

This is the same result as
[Choosing after seeing the state is worth at least the best commitment](../../choice-and-utility/expected-value-of-perfect-information/evpi-nonneg.md).
Here it is written as an inequality; the linked page writes it as a nonnegative difference.
