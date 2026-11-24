# An estimate always below κλ with κ < 1 is strictly anti-conservative

Let `Z` be a score with law `𝒩(0, λ)` under `P`, for some `λ > 0`, and let `L` be a real function on
the sample space with `0 < L(ω) ≤ κ λ` at every sample point `ω`, for some `κ < 1`. Then dividing by
`L` is strictly anti-conservative at every positive threshold: for every `c > 0`,

`P(Z² / L > c) > P(χ²₁ > c)`,

where `P(χ²₁ > c)` is the [`χ²₁` tail](../../../Biology/statistical-genetics/association-tests/genomic-control/chi-sq-one-tail.md). Nothing is assumed about the joint law
of `Z` and `L`, and `L` need not be measurable: `P` of a set that is not measurable is its outer
measure.
