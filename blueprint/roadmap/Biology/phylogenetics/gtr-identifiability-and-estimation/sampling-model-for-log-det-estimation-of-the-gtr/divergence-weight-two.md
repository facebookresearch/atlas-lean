# Explicit two-state GTR divergence weights

On the two states `0` and `1`, let `π` be real base frequencies with `π 0 + π 1 = 1` and `s` a
symmetric real `2 × 2` matrix, and write `Q` for the
[GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`. Then for every real `t` the
[divergence weight](../identifiability-of-the-gtr-model/gtr-pair-law.md)
`w(i, j) = π i · exp (t · Q) i j` of a site pair is `w(i, j) = π i · (e · [i = j] + (1 - e) · π j)`
with `e = exp (-(s 0 1 · t))`, where `[i = j]` is `1` if `i = j` and `0` otherwise. These are the
raw, possibly negative weights; when moreover `π 0, π 1 ≥ 0`, `s 0 1 ≥ 0` and `t ≥ 0` they are the
masses that the [GTR divergence law](divergence-law.md) gives the singletons, when singletons are
measurable.
