# Parameters with the true GTR pair-site law lie in the identified class

Let `ι` be a finite set of states and let `π`, `s` and `t` give each parameter `θ` base frequencies
`π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι` matrix) and a branch length `t θ > 0`, with
every `(π θ, s θ)` in the
[GTR parameter domain](../gtr-identifiability-and-estimation/identifiability-of-the-gtr-model/is-gtrparam.md): `π θ i > 0`,
`∑_i π θ i = 1`, `s θ` symmetric and `s θ i j > 0` for `i ≠ j`. Then for every `θ₀`, every parameter
`θ` with the same [pair-site law](gtr-law.md) as `θ₀` lies in the [identified class](gtr-class.md)
of `θ₀`: `π θ = π θ₀` and `t θ · s θ i j = t θ₀ · s θ₀ i j` for all `i ≠ j`. This is the
identifiability hypothesis of the general consistency theorems for the pair-site model, with the
identified class as `E`.
