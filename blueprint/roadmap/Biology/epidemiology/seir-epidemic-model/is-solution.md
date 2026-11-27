# Solution of the closed SEIR system for times t ≥ 0

Let `β`, `σ`, `γ` and `N` be real numbers; no sign or nonzero condition is imposed on them.
Functions `S, E, I, R : ℝ → ℝ` solve the closed SEIR system with transmission rate `β`, rate `σ` of
leaving the latent class, removal rate `γ` and population size `N` if, at every time `t ≥ 0`, each
of them has a two-sided derivative at `t`, with

`S'(t) = -β S(t) I(t) / N`, `E'(t) = β S(t) I(t) / N - σ E(t)`,

`I'(t) = σ E(t) - γ I(t)`, `R'(t) = γ I(t)`,

where the quotient by `N` is read as `0` when `N = 0`. No initial condition is part of the
definition, and negative times enter only through the two-sided derivative at `t = 0`. Nor is `N`
tied to the compartments: `S(t) + E(t) + I(t) + R(t)` need not equal `N`. In applications `β ≥ 0`,
`σ, γ, N > 0`, and the compartments are nonnegative with total `N`.
