# GTR divergence law on site pairs

Let `ι` be a finite set of states. For real base frequencies `π`, exchangeabilities `s` and a branch
length `t` with [divergence weight](../identifiability-of-the-gtr-model/gtr-pair-law.md)
`w(i, j) = π i · exp (t · Q) i j`, the GTR divergence law is the weighted sum of Dirac measures
`μ = ∑_a max (w(a), 0) · δ_a` over the site pairs `a ∈ ι × ι`, a measure for the product σ-algebra
on `ι × ι` built from any σ-algebra on `ι`. It is defined for all real parameters: a negative weight
is clamped to `0`, so the Dirac measure at its pair gets coefficient `0`. When every singleton is
measurable, the mass of `{a}` is `max (w(a), 0)`; otherwise a singleton need not be measurable and
its outer measure can be positive even when its coefficient is `0`. It is a probability measure
when, for example, `π i ≥ 0`, `∑_i π i = 1`, `s i j ≥ 0` for `i ≠ j` and `t ≥ 0`.
