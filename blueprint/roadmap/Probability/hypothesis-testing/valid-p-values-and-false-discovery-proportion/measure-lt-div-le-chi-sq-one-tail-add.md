# Upper tail bound for Z²/L when L ≥ κλ on a set E

Let `Z` be a score with law `𝒩(0, λ)` under `P`, for some `λ > 0` (so `P` is a probability measure),
and let `L` be any real function on the sample space, for example an estimate of `λ` (mean, median,
leave-one-out). Let `κ > 0` and let `E` be a set of sample points on which `L ≥ κ λ` (for example
`κ = 1 - δ`). Then for every `c ≥ 0`,

`P(Z² / L > c) ≤ P(χ²₁ > c κ) + P(Eᶜ)`,

where `P(χ²₁ > c κ)` is the [`χ²₁` tail](../../../Biology/statistical-genetics/association-tests/genomic-control/chi-sq-one-tail.md). Nothing is assumed about `L` outside
`E`, where it may vanish (then `Z² / L = 0` by the convention `x / 0 = 0`), nor about the joint law
of `Z` and `L`. Neither `L` nor `E` need be measurable: `P` of a set that is not measurable is its
outer measure.
