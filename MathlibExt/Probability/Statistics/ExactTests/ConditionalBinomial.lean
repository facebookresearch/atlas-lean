/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.TransmissionTest
public import MathlibExt.Probability.Statistics.GLM.CountData.ExactTest

/-!
# Conditional-binomial exact tests with a random total: TDT and McNemar

The exact one-sided TDT and McNemar p-values of
`MathlibExt.Biology.StatisticalGenetics.TransmissionTest` are binomial upper tails
`P(Bin(d, 1/2) ≥ B)` for a *fixed* number `d` of informative transmissions (TDT) or discordant
pairs (McNemar). In a study the total is itself random: `D ω` informative transmissions, or
`X ω + Y ω` discordant pairs. The test then evaluates the p-value at the observed total,
`ω ↦ tdtPValue (D ω) B ω`. This file proves that this statistic is valid unconditionally.

## Setting

* **Conditioning.** On each event `{ω | D ω = d}` (for McNemar, `D = X + Y`) of positive
  probability, through the conditional measure `μ[|{ω | D ω = d}]`. Totals of probability zero
  are allowed and impose nothing.
* **Null hypothesis.** Stated as a hypothesis on conditional laws: given each total `D = d` of
  positive probability, `B ~ Bin(d, 1/2)`. In the Poissonized McNemar model (`X ~ Po(r)`,
  `Y ~ Po(r)` independent, `r ≥ 0`) no such hypothesis is needed: validity is the merged
  `GLM.CountData.isValidPValue_countExactPValue` with library sizes `s₁ = s₂ = 1`. The
  conditional law in the fixed-number-of-pairs multinomial model is **not** derived here; that
  model is covered only through the hypothesis of `isValidPValue_mcnemarPValue_total_of_cond`.
* **p-value.** `tdtPValue (D ω) B ω = P(Bin(D ω, 1/2) ≥ B ω)` and
  `mcnemarPValue (X ω + Y ω) X ω = P(Bin(X ω + Y ω, 1/2) ≥ X ω)`, one-sided (excess
  transmission, excess of the first discordant type).

## Main results

* `isValidPValue_tdtPValue_total_of_cond`: if, given each total `D = d` of positive probability,
  `B ~ Bin(d, 1/2)`, then the TDT p-value at the observed total is valid.
* `isValidPValue_mcnemarPValue_total_of_cond`: the same for McNemar with `D = X + Y`.
* `isValidPValue_mcnemarPValue_total`: under the equal-rate Poisson null (`r ≥ 0`), the McNemar
  p-value at the observed number of discordant pairs is valid.

## References

* R. S. Spielman, R. E. McGinnis and W. J. Ewens, *Transmission test for linkage
  disequilibrium: the insulin gene region and insulin-dependent diabetes mellitus (IDDM)*,
  Am. J. Hum. Genet. 52 (1993), 506–516.
* Q. McNemar, *Note on the sampling error of the difference between correlated proportions or
  percentages*, Psychometrika 12 (1947), 153–157.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  §4.6 and Lemma 3.3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Biology.StatisticalGenetics.TransmissionTest
open scoped unitInterval NNReal ENNReal

namespace MathlibExt.Probability.Statistics.ExactTests

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **TDT with a random number of informative transmissions.** Let `D ω` be the number of
informative transmissions (from heterozygous parents) and `B ω` the number that pass on the
allele of interest. If, given each value `D = d` of positive probability, `B ~ Bin(d, 1/2)` (the
null of no linkage, with the transmissions treated as independent fair coins given `d`), then
the TDT p-value evaluated at the observed total, `ω ↦ P(Bin(D ω, 1/2) ≥ B ω)`, is valid under
`μ`. This is the generic averaging lemma `isValidPValue_of_forall_cond_of_ne_zero` (over the
values of `D`) applied to the fixed-`d` guarantee `isValidPValue_tdtPValue`. -/
theorem isValidPValue_tdtPValue_total_of_cond [IsProbabilityMeasure μ] {D B : Ω → ℕ}
    (hDm : Measurable D)
    (hcond : ∀ d, μ {ω | D ω = d} ≠ 0 → HasLaw B Bin(d, fairCoin) (μ[|{ω | D ω = d}])) :
    IsValidPValue μ (fun ω => tdtPValue (D ω) B ω) :=
  isValidPValue_of_forall_cond_of_ne_zero (q := fun d => tdtPValue d B) hDm
    (ae_of_all μ fun _ => rfl) fun d hd => isValidPValue_tdtPValue (hcond d hd)

/-- **McNemar's test with a random number of discordant pairs.** Let `X ω` and `Y ω` count the
discordant pairs of the two types. If, given each number `X + Y = N` of discordant pairs of
positive probability, `X ~ Bin(N, 1/2)`, then the McNemar p-value at the observed number of
discordant pairs, `ω ↦ P(Bin(X ω + Y ω, 1/2) ≥ X ω)`, is valid under `μ`.

The conditional law is a hypothesis. The Poissonized model does not need it:
`isValidPValue_mcnemarPValue_total` gets validity there from
`GLM.CountData.isValidPValue_countExactPValue`. In the model with a fixed number of pairs and
multinomial cell counts the conditional law is **not** derived here, and that model is reachable
only through this hypothesis. -/
theorem isValidPValue_mcnemarPValue_total_of_cond [IsProbabilityMeasure μ] {X Y : Ω → ℕ}
    (hXm : Measurable X) (hYm : Measurable Y)
    (hcond : ∀ N, μ {ω | X ω + Y ω = N} ≠ 0 →
      HasLaw X Bin(N, fairCoin) (μ[|{ω | X ω + Y ω = N}])) :
    IsValidPValue μ (fun ω => mcnemarPValue (X ω + Y ω) X ω) :=
  isValidPValue_tdtPValue_total_of_cond (D := fun ω => X ω + Y ω) (hXm.add hYm) hcond

/-- **McNemar's test under the equal-rate Poisson null.** Let the discordant counts `X ~ Po(r)`
and `Y ~ Po(r)` be independent with a common rate `r ≥ 0` (the Poissonized null of marginal
homogeneity). Then the McNemar p-value at the observed number of discordant pairs,
`ω ↦ P(Bin(X ω + Y ω, 1/2) ≥ X ω)`, is valid under `μ`, whatever `r`. The same statement is the
TDT when `X` and `Y` are the transmitted and untransmitted counts *modeled* as independent
Poisson counts with equal rates; that is a statistical model of the counts, not a consequence of
Mendelian segregation. This is the merged `GLM.CountData.isValidPValue_countExactPValue` with
library sizes `s₁ = s₂ = 1`, restated for `mcnemarPValue`. -/
theorem isValidPValue_mcnemarPValue_total {X Y : Ω → ℕ} {r : ℝ≥0} (hXm : Measurable X)
    (hYm : Measurable Y) (hX : HasLaw X (poissonMeasure r) μ) (hY : HasLaw Y (poissonMeasure r) μ)
    (hXY : IndepFun X Y μ) :
    IsValidPValue μ (fun ω => mcnemarPValue (X ω + Y ω) X ω) := by
  have := hX.isProbabilityMeasure
  have hfc : GLM.CountData.libraryFraction 1 1 = fairCoin := by
    apply Subtype.ext
    rw [GLM.CountData.coe_libraryFraction, coe_fairCoin]
    norm_num
  have hval := GLM.CountData.isValidPValue_countExactPValue (s₁ := 1) (s₂ := 1) (r := r)
    (by norm_num) hXm hYm (by rwa [one_mul]) (by rwa [one_mul]) hXY
  convert hval using 2 with ω
  rw [GLM.CountData.countExactPValue, GLM.CountData.countExactTail, hfc]
  rfl

end MathlibExt.Probability.Statistics.ExactTests
