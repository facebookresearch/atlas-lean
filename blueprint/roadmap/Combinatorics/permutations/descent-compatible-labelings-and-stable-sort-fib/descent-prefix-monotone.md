# Descent prefixes are nondecreasing

Let `N : ℕ`, `σ ∈ S_N`, and `Des(σ)` be its adjacent descent positions. Put `d = descentNumber
σ` and `r_i = |{j ∈ Des(σ) | j<i}|`. A descent labeling in alphabet `Fin m` is a nondecreasing
`g : Fin N → Fin m` with `g(j)<g(j+1)` at each descent. The natural-number function `i ↦
descentPrefix σ i` is monotone on `Fin N`.
