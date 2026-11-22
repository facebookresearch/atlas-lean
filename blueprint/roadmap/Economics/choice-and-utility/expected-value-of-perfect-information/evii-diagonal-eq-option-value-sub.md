# Value of perfect information: option value minus best commitment

Let `Ω` be a finite set of states with nonnegative weights `p(ω) ≥ 0`, `A` a finite nonempty set of
actions and `U(a, ω)` the payoff of action `a` in state `ω`. The value of information with evidence
weights `w(ω, e)`, `∑ₑ maxₐ ∑_ω w(ω, e) U(a, ω) - maxₐ ∑_ω ∑ₑ w(ω, e) U(a, ω)`, takes for the
diagonal weights `w(ω, e) = p(ω)` if `e = ω` and `0` otherwise (the evidence reveals the state) the
value `∑_ω p(ω) maxₐ U(a, ω) - maxₐ ∑_ω p(ω) U(a, ω)`: the real option value minus the best
commitment.
