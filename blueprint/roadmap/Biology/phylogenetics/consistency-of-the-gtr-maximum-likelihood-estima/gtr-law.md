# Site-pattern law of the GTR pair-site model

Let `ι` be a finite set of states, and let `π`, `s` and `t` give each parameter `θ` of a set `Θ`
base frequencies `π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι` matrix) and a branch length
`t θ ∈ ℝ`. The GTR pair-site model gives `θ` the weights
`law θ (i, j) = π θ i · exp (t θ · Q_θ) i j` of the aligned site patterns `(i, j)` of two taxa
joined by one branch: the [pair-site law](../identifiability-of-the-gtr-model/gtr-pair-law.md) of
`(π θ, s θ, t θ)`, indexed by pairs of states. Here `Q_θ` is the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π θ` and exchangeabilities `s θ`. The weights are defined for all real parameters. They
form a probability law on pairs of states when, for example, `(π θ, s θ)` lies in the
[GTR parameter domain](../identifiability-of-the-gtr-model/is-gtrparam.md): `π θ i > 0`,
`∑_i π θ i = 1`, `s θ` symmetric and `s θ i j > 0` for `i ≠ j`, the diagonal of `s θ` being free,
and `t θ ≥ 0`.
