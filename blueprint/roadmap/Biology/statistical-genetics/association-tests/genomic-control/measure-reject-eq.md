# Genomic control is exactly calibrated in the common-inflation model

Consider a [common-inflation model](common-inflation-model.md) on a measure `P`, with inflation
factor `λ > 0` and null scores `Z_j`, each with law `𝒩(0, λ)` under `P`. For every marker `j`
and every real threshold `c`,

`P(Z_j² / λ > c) = P(χ²₁ > c)`:

the test that rejects marker `j` when its corrected statistic `χ²_j / λ = Z_j² / λ` exceeds `c`
has rejection probability equal to the [`χ²₁` tail](chi-sq-one-tail.md) at `c`.
