# Calibrated with the true λ, strictly conservative with λ̂ at c ≥ m

Take the [common-inflation model](../../../Biology/statistical-genetics/association-tests/genomic-control/common-inflation-model.md) with `m` genes: under the measure `P`,
every score `Z_k` has law `𝒩(0, λ)` for one common `λ > 0`, and nothing is assumed about the joint
law of the scores. For every gene `j`:

- dividing by the true `λ` is calibrated at every threshold: `P(Z_j² / λ > c) = P(χ²₁ > c)` for
  every real `c`;
- dividing by the [mean estimate](lambda-hat.md) `λ̂` of the same scores is not: the [corrected
  statistic](gc-stat-rv.md) satisfies `P(T_j > c) < P(χ²₁ > c)` at every threshold `c ≥ m`.

Here `P(χ²₁ > c)` is the [`χ²₁` tail](../../../Biology/statistical-genetics/association-tests/genomic-control/chi-sq-one-tail.md). No independence or other assumption on
the dependence between the scores is needed for either part.
