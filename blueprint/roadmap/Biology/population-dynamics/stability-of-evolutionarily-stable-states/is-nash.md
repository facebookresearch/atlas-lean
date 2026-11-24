# Symmetric Nash equilibrium of a matrix game

For a finite set `ι` of strategies and a payoff matrix `A` on `ι`, a vector `p : ι → ℝ` is a
symmetric Nash equilibrium when `p` is a mixed strategy (`p_i ≥ 0` for every `i` and
`∑_i p_i = 1`) and every mixed strategy `q` satisfies `q · A p ≤ p · A p`: no mixed strategy earns
more against `p` than `p` itself.
