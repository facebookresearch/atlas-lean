# Law of large numbers for the epidemic

**Law of large numbers for the epidemic** (Janson, Luczak and Windridge 2014,
Theorems 2.6(c)–(d) and 2.7). Assume the degree conditions (D1)–(D6) (`Conditions`), `β > 0`,
`ρ ≥ 0` and `μ_I > 0`, and for the simple graph (`simple = true`) also (G1)
(`SquareSumBound`). Let `θ` solve `θ' = -β θ p_I(θ)`, `θ_0 = 1`, let `θ_∞ ∈ (0, 1)` be the
zero of `h_I`, and let `Î` be the solution of Eq. (2.20) (`infectiveLimit`). Then for every
`ε > 0`, the probability that for some `t ≥ 0` one of `|S_t/n - v_S(θ_t)|`, `|I_t/n - Î_t|`,
`|R_t/n - (1 - v_S(θ_t) - Î_t)|`, `|X_{S,t}/n - h_S(θ_t)|` exceeds `ε` tends to `0`, and the
probability that `|S_∞/n - v_S(θ_∞)| > ε` tends to `0`, for the epidemic on the configuration
multigraph (`simple = false`) or on the uniform simple graph (`simple = true`). (`hQ` records
that each epidemic rate matrix is a rate matrix.)

## Sources

- Janson, Luczak and Windridge (2014), Theorems 2.6 and 2.7.
