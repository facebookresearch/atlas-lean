# Lower tail bound for Z²/L when 0 < L ≤ κλ on a set E

Let `Z` be a score with law `𝒩(0, λ)` under `P`, for some `λ > 0` (so `P` is a probability measure),
let `L` be any real function on the sample space, `κ` a real number and `E` a set of sample points
on which `0 < L ≤ κ λ` (for example `κ = 1 + δ`). Then for every `c ≥ 0`,

`P(χ²₁ > c κ) ≤ P(Z² / L > c) + P(Eᶜ)`,

where `P(χ²₁ > c κ)` is the [`χ²₁` tail](../../../Biology/statistical-genetics/association-tests/genomic-control/chi-sq-one-tail.md). Nothing is assumed about `L` outside
`E`, nor about the joint law of `Z` and `L`. Neither `L` nor `E` need be measurable: `P` of a set
that is not measurable is its outer measure.
