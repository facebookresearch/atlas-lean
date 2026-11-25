# Site-pair probabilities are the GTR divergence weights

Let `ι` be a finite set of states. Let every subset of `ι` be measurable. If `(π, s, t)` are
[sampling parameters](is-sampling-params.md): `π i ≥ 0` for every `i`, `∑_i π i = 1`, `s i j ≥ 0`
for `i ≠ j` and `t ≥ 0`, then under the [sample law](sample-law.md) `S` the [site pair](site.md)
`ω ↦ ω n` equals `a` with probability the [divergence weight](../identifiability-of-the-gtr-model/gtr-pair-law.md)
`w(i, j) = π i · exp (t · Q) i j`: `S {ω : ω n = a} = w(a)` for every `n` and every `a ∈ ι × ι`.
