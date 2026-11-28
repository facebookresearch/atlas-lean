# Sampling parameters of the GTR divergence law

Let `ι` be a finite set of states. Real base frequencies `π : ι → ℝ`, exchangeabilities `s` (a real
`ι × ι` matrix) and a branch length `t` are sampling parameters if `π i ≥ 0` for every `i`,
`∑_i π i = 1`, `s i j ≥ 0` for `i ≠ j` and `t ≥ 0`. These conditions ensure, without being
necessary, that the [GTR divergence law](divergence-law.md) `μ = ∑_a max (w(a), 0) · δ_a` is a
probability measure, where `w(i, j) = π i · exp (t · Q) i j` and `Q` is the
[GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md). Symmetry of `s` is
not required.
