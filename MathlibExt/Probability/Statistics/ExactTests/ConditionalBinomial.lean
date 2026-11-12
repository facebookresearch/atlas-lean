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
  positive probability, `B ~ Bin(d, 1/2)`. For McNemar's test this conditional law is derived
  here only in the Poissonized model (`X ~ Po(r)`, `Y ~ Po(r)` independent, `r ≥ 0`), from the
  merged `GLM.CountData.hasLaw_cond_binomial_libraryFraction`. The conditional law in the
  fixed-number-of-pairs multinomial model is **not** derived here; that model is covered only
  through the hypothesis of `isValidPValue_mcnemarPValue_total_of_cond`.
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
`μ`. The proof averages the fixed-`d` guarantee `isValidPValue_tdtPValue` over `D`. -/
theorem isValidPValue_tdtPValue_total_of_cond [IsProbabilityMeasure μ] {D B : Ω → ℕ}
    (hDm : Measurable D)
    (hcond : ∀ d, μ {ω | D ω = d} ≠ 0 → HasLaw B Bin(d, fairCoin) (μ[|{ω | D ω = d}])) :
    IsValidPValue μ (fun ω => tdtPValue (D ω) B ω) := by
  intro s hs
  set E : ℕ → Set Ω := fun d => {ω | D ω = d} with hE
  have hEm : ∀ d, MeasurableSet (E d) := fun d => hDm (measurableSet_singleton d)
  have hEd : Pairwise (Function.onFun Disjoint E) :=
    fun a b hab => Set.disjoint_left.2 fun ω ha hb => hab (ha.symm.trans hb)
  have hEu : (⋃ d, E d) = Set.univ := Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨_, rfl⟩
  have hterm : ∀ d, μ (E d ∩ {ω | tdtPValue (D ω) B ω ≤ s}) ≤ ENNReal.ofReal s * μ (E d) := by
    intro d
    by_cases hd : μ (E d) = 0
    · rw [hd, mul_zero]
      exact (measure_mono Set.inter_subset_left).trans hd.le
    have hset : E d ∩ {ω | tdtPValue (D ω) B ω ≤ s} = E d ∩ {ω | tdtPValue d B ω ≤ s} := by
      ext ω
      simp only [hE, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₁ ▸ h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₁ ▸ h₂⟩⟩
    rw [hset, ← cond_mul_eq_inter (hEm d)]
    exact mul_le_mul_left (isValidPValue_tdtPValue (hcond d hd) s hs) _
  calc μ {ω | tdtPValue (D ω) B ω ≤ s}
      = μ (⋃ d, E d ∩ {ω | tdtPValue (D ω) B ω ≤ s}) := by
        rw [← Set.iUnion_inter, hEu, Set.univ_inter]
    _ ≤ ∑' d, μ (E d ∩ {ω | tdtPValue (D ω) B ω ≤ s}) := measure_iUnion_le _
    _ ≤ ∑' d, ENNReal.ofReal s * μ (E d) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal s := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion hEd hEm, hEu, measure_univ, mul_one]

/-- **McNemar's test with a random number of discordant pairs.** Let `X ω` and `Y ω` count the
discordant pairs of the two types. If, given each number `X + Y = N` of discordant pairs of
positive probability, `X ~ Bin(N, 1/2)`, then the McNemar p-value at the observed number of
discordant pairs, `ω ↦ P(Bin(X ω + Y ω, 1/2) ≥ X ω)`, is valid under `μ`.

The conditional law is a hypothesis. It is derived in the Poissonized model
(`isValidPValue_mcnemarPValue_total`); in the model with a fixed number of pairs and multinomial
cell counts it is **not** derived here, and that model is reachable only through this
hypothesis. -/
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
Mendelian segregation. -/
theorem isValidPValue_mcnemarPValue_total {X Y : Ω → ℕ} {r : ℝ≥0} (hXm : Measurable X)
    (hYm : Measurable Y) (hX : HasLaw X (poissonMeasure r) μ) (hY : HasLaw Y (poissonMeasure r) μ)
    (hXY : IndepFun X Y μ) :
    IsValidPValue μ (fun ω => mcnemarPValue (X ω + Y ω) X ω) := by
  have := hX.isProbabilityMeasure
  have hfc : GLM.CountData.libraryFraction 1 1 = fairCoin := by
    apply Subtype.ext
    rw [GLM.CountData.coe_libraryFraction, coe_fairCoin]
    norm_num
  refine isValidPValue_mcnemarPValue_total_of_cond hXm hYm fun N hN => ?_
  rw [← hfc]
  exact GLM.CountData.hasLaw_cond_binomial_libraryFraction (by norm_num) hXm hYm
    (by rwa [one_mul]) (by rwa [one_mul]) hXY hN

end MathlibExt.Probability.Statistics.ExactTests
