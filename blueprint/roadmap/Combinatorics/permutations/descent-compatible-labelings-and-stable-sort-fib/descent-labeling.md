# Labels that rise strictly at descents

Let `N : ℕ`, `σ ∈ S_N`, and `Des(σ)` be its adjacent descent positions. Put `d = descentNumber
σ` and `r_i = |{j ∈ Des(σ) | j<i}|`. A descent labeling in alphabet `Fin m` is a nondecreasing
`g : Fin N → Fin m` with `g(j)<g(j+1)` at each descent. `DescentLabeling σ m` is the subtype
of labelings with these monotonicity and strict-descent-rise conditions.
