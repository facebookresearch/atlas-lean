# Cochran–Armitage statistic of the first N subjects

Let `S_m(ω) = (G_m(ω), Y_m(ω))` be the pair of the genotype class `G_m(ω) ∈ {0, 1, 2}` and the case
status `Y_m(ω)` (true for a case, false for a control) of subject `m = 0, 1, 2, …` at the outcome
`ω`. For `N ∈ ℕ`, the Cochran–Armitage statistic `T_N(ω)` is the
[trend statistic](../../genomic-prediction-from-summary-statistics/trend-stat.md) of the `2 × 3`
table of the first `N` subjects, with the [case counts](case-count.md) `rᵢ = rᵢ(N, ω)` and the
[control counts](control-count.md) `sᵢ = sᵢ(N, ω)`: `T = N U² / (R S (N ∑ᵢ i² nᵢ − (∑ᵢ i nᵢ)²))`,
where `N` is the total count, `R = ∑ᵢ rᵢ` and `S = ∑ᵢ sᵢ` are the numbers of cases and controls,
`nᵢ = rᵢ + sᵢ` and `U = ∑ᵢ i (rᵢ S − sᵢ R)`. With the convention `x / 0 = 0`, `T_N(ω) = 0` when the
denominator vanishes: when there are no cases, no controls, or all `N` subjects are in one genotype
class (in particular for `N = 0`); the classical statistic is undefined there.
