# Value of the option to act after observing the state

For a finite nonempty set of feasible actions, a finite set of states `Ω` with real weights
`p(ω)` (probabilities in the intended reading; the definition imposes no condition) and payoffs
`V(a, ω)`, the value of the option to choose, after seeing the state, the best feasible action is
the expected statewise maximum `E[max_a V_a] = ∑_{ω ∈ Ω} p(ω) * max_a V(a, ω)` (Raiffa and
Schlaifer, Chapter 4, Section 5). The set of actions must be nonempty so that the statewise
maximum exists.
