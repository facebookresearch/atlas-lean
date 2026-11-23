# Site-pattern law of the GTR pair-site model

Let `ι` be a finite set of states, and let `π`, `s` and `t` give each parameter `θ` of a set `Θ`
base frequencies `π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι` matrix) and a branch length
`t θ ∈ ℝ`. The GTR pair-site model gives `θ` the law of an aligned site pattern `(i, j)` for two
taxa joined by one branch, the [pair-site law](../identifiability-of-the-gtr-model/gtr-pair-law.md)
`law θ (i, j) = π θ i · exp (t θ · Q_θ) i j`, where `Q_θ` is the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π θ` and exchangeabilities `s θ`. It is defined for all real parameters; when
`(π θ, s θ)` lies in the [GTR parameter domain](../identifiability-of-the-gtr-model/is-gtrparam.md)
and `t θ ≥ 0`, it is a probability law on pairs of states.
