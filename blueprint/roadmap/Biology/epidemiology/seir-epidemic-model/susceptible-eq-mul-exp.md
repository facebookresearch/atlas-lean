# Susceptibles in integrating-factor form

Let `(S, E, I, R)` be a [solution of the SEIR system](is-solution.md), with any real parameters
`β`, `σ`, `γ`, `N`. Then for every `t ≥ 0`,

`S(t) = S(0) exp(-∫₀ᵗ β I(s) / N ds)`.

Here `β I(s) / N` is read as `0` when `N = 0`, and then `S(t) = S(0)`.
