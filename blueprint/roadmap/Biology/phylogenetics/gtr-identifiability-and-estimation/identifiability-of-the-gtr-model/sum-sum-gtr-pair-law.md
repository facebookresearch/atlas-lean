# The pair-site law has total mass one for every branch length

Let `ι` be a finite set of states. If `(π, s)` lies in the [GTR parameter domain](is-gtrparam.md),
`π i > 0` for every `i`, `∑_i π i = 1`, `s` symmetric and `s i j > 0` for `i ≠ j`, the diagonal of
`s` being free, then for every real branch length `t` the [pair-site law](gtr-pair-law.md)
`F(π, s, t) i j = π i · exp (t · Q(π, s)) i j` sums to `1` over pairs of states:
`∑_i ∑_j F(π, s, t) i j = 1`, where `Q(π, s)` is the
[GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md). This is only a
total-mass identity; together with the [nonnegativity for `t ≥ 0`](gtr-pair-law-nonneg.md) it makes
the pair-site law a probability law on pairs of states.
