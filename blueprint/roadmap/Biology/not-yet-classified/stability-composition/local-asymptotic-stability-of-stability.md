# Local asymptotic stability from the complex-balanced results

Let `N` be a weakly
reversible mass-action network of deficiency zero with positive rate constants `k`, and let `x₀`
be a positive state. Assume three statements about every network on the species `S` and the
reactions `ρ` with positive rate constants, a positive complex-balanced point `cstar` and a
positive equilibrium `xstar`: `hCB1`, every state of the stoichiometric compatibility class of
`xstar` close enough to it starts a solution on `[0, ∞)`; `hCB2`, for every `ε > 0`, every
solution that starts in that class close enough to `xstar` stays within `ε` of it; and `hCB3`,
every solution that starts in that class close enough to `xstar` converges to it. Then the class
of `x₀` contains exactly one positive equilibrium, and every positive equilibrium `xstar` in
that class has the three properties for `N` and `k`. The deficiency-zero theorem supplies
`cstar`; `localAsymptoticStability` applies this with `exists_solution_of_near`, `stable` and
`attractive`.
