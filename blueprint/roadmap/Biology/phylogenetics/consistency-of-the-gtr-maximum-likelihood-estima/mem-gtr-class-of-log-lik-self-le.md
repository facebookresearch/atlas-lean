# Expected GTR log-likelihood maximizers lie in the identified class

Let `ι` be a finite set of states and let `π`, `s` and `t` give each parameter `θ` base frequencies
`π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι` matrix) and a branch length `t θ > 0`, with
every `(π θ, s θ)` in the
[GTR parameter domain](../identifiability-of-the-gtr-model/is-gtrparam.md): `π θ i > 0`,
`∑_i π θ i = 1`, `s θ` symmetric and `s θ i j > 0` for `i ≠ j`. Write `law θ` for the
[pair-site law](gtr-law.md) of `θ`. Then every `θ` at which the expected log-likelihood under
`law θ₀` is at least its value at `θ₀`,
`∑_a law θ₀ a · log (law θ a) ≥ ∑_a law θ₀ a · log (law θ₀ a)` (sums over pairs of states `a`), lies
in the [identified class](gtr-class.md) of `θ₀`.
