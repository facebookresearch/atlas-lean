# Derivative of the infected total E + I along a solution

Let `(S, E, I, R)` be a [solution of the SEIR system](is-solution.md) with `γ ≠ 0` and `N ≠ 0`
(`β` and `σ` arbitrary), and write `R₀ = β / γ`. Then at every time `t ≥ 0` the infected total
`E + I` has derivative

`(E + I)'(t) = γ I(t) (R₀ S(t) / N - 1) = β S(t) I(t) / N - γ I(t)`:

the transfer `σ E` from `E` to `I` does not change it.
