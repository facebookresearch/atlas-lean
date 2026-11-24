# The GTR pair-site law is positive for positive branch lengths

Let `ι` be a finite set of states and let `π`, `s` and `t` give each parameter `θ` base frequencies
`π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι` matrix) and a branch length `t θ > 0`, with
every `(π θ, s θ)` in the
[GTR parameter domain](../identifiability-of-the-gtr-model/is-gtrparam.md): `π θ i > 0`,
`∑_i π θ i = 1`, `s θ` symmetric and `s θ i j > 0` for `i ≠ j`. Then the [pair-site law](gtr-law.md)
of every parameter is positive: `π θ i · exp (t θ · Q_θ) i j > 0` for every `θ` and every pair of
states `(i, j)`, where `Q_θ` is the GTR rate matrix of `(π θ, s θ)`.
