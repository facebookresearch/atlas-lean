# Is Stationary Master Solution

`p` solves the **stationary chemical master equation** (the stationary Kolmogorov forward
equation `p Q = 0`) of the stochastic mass-action chain with rate constants `κ`: at every state
`x` the probability flux out, `p x ∑_r λ_r(x)`, equals the flux in, one term
`p w λ_r(w)` for each reaction `r` with `prod r ≤ x` from its unique predecessor
`w = unfire N r x` (`fire_eq_iff`). The equation is defined for all real `κ`; it is the master
equation of a chain when `κ ≥ 0`, as `ergodic_of_isComplexBalanced` assumes.
