# Identifiability of the GTR pair-site model, exact form

Let `ι` be a finite set of states and let `π`, `s` and `t` give each parameter `θ` base frequencies
`π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι` matrix) and a branch length `t θ > 0`, with
every `(π θ, s θ)` in the
[GTR parameter domain](../gtr-identifiability-and-estimation/identifiability-of-the-gtr-model/is-gtrparam.md): `π θ i > 0`,
`∑_i π θ i = 1`, `s θ` symmetric and `s θ i j > 0` for `i ≠ j`. Then for all parameters `θ₀` and
`θ`, `θ` has the same [pair-site law](gtr-law.md) as `θ₀` if and only if `θ` lies in the
[identified class](gtr-class.md) of `θ₀`, that is, `π θ = π θ₀` and
`t θ · s θ i j = t θ₀ · s θ₀ i j` for all `i ≠ j`.
