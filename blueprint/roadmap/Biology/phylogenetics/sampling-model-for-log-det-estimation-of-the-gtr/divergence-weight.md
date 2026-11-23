# GTR divergence weight of a site pair

Let `ι` be a finite set of states. For real base frequencies `π : ι → ℝ`, a real `ι × ι` matrix `s`
of exchangeabilities and a real branch length `t`, the GTR divergence weight of the site pair
`(i, j)` is `w(i, j) = π i · exp (t · Q) i j`, where `Q` is the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`. It is defined for all real parameters; for `t < 0` it can
be negative.
