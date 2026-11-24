# The pair-site law is nonnegative for nonnegative branch lengths

Let `ι` be a finite set of states. If `(π, s)` lies in the [GTR parameter domain](is-gtrparam.md),
`π i > 0` for every `i`, `∑_i π i = 1`, `s` symmetric and `s i j > 0` for `i ≠ j`, the diagonal of
`s` being free, and `t ≥ 0`, every entry of the [pair-site law](gtr-pair-law.md) is nonnegative:
`π i · exp (t · Q(π, s)) i j ≥ 0` for all states `i`, `j`, where `Q(π, s)` is the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md).
