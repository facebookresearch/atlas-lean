/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Omics.AllelicImbalanceQualityCorrection
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Tests for the quality correction constant for allelic imbalance.

* **Bins.** With the source's base `b = 1.05`, `C̄_1 = C̄_14 = 2` and `C̄_15 = 3`, so bins `2` to
  `14` are empty and bin `15` is `(2, 3]`, with `Ĉ_15 = √6` and `3` reads; with `b = 2` the bin
  `(1, 2]` is bin `1`, with `Ĉ_1 = √2` and `2` reads.
* **The pooled law.** For `ω₁ = 1/2`, `α₁ = 2`, `α₂ = 1/2` and one read per replicate,
  `BB(2; 2, 2)(1) = 2/5` and `BB(2; 1/2, 1/2)(1) = 1/4`, so the pooled count `1` has probability
  `13/40`.
* **The M-step.** `BetaBin(2, 2, 2)` has variance `2 (4 + 2) / (4 · 5) = 3/5`, and the
  moment-matching shape of `3/5` is `((2)² - 4 · 3/5) / (8 · 3/5 - 4) = 2`. With no reads the
  formula gives `-1/2` for every nonzero variance, and `0` at variance `0`.
* **The expected law.** For the mixture `θ₀` that is `BetaBin(·, 2, 2)` alone (`ω₁ = 1`) and two
  reads per replicate, the pooled count of `4` reads has law `1/7, 8/35, 9/35, 8/35, 1/7`, the
  pair `(j₁, j₂)` has probability `C(2, j₁) C(2, j₂) / C(4, j₁ + j₂)` times that of `j₁ + j₂`,
  and `ΔAI = |j₁ - j₂| / 2` is `0`, `1/2` or `1` with probabilities `16/35`, `16/35`, `3/35`. Its
  quantiles at `1/5`, `1/2` and `19/20` are `0`, `1/2` and `1`. The pair `(0, 0)` has the
  probability `1/7` of the simulated law, `p ~ Beta(2, 2)` and two independent `Bin(2, p)`.
* **An end-to-end QCC.** Four genes with two reads in each of two replicates, so mean coverage `2`
  in bin `1` of base `2`: one with AIs `1/2` and `1` and three with AIs `1` and `0`. The observed
  `ΔAI` is `1/2` once and `1` three times, with quantiles `1/2`, `1`, `1` at `1/5`, `1/2`,
  `19/20`. The ratio at `1/5` is undefined (`Q^exp = 0`) and left out; the others are
  `1 / (1/2) = 2` and `1 / 1 = 1`, so the QCC is `3/2`, and the effective coverage of a gene of
  coverage `9` is `9 / (3/2) ^ 2 = 4`.
* **More replicates.** Three replicates have `3` pairs, and the QCC is the mean of the three
  pairwise QCCs, each with its own bins; with two, the QCC is the pair's; with one, it is `0`.
* **Junk values.** A fit with no defined ratio is `0`, and an empty bin contributes nothing. -/

open MeasureTheory ProbabilityTheory Finset
open Domains.Biology.Omics.AllelicImbalance

namespace DomainsTest.Biology.Omics.AllelicImbalanceQualityCorrection

/-! ### Bins -/

example : coverageBinBoundary (21 / 20) 1 = 2 ∧ coverageBinBoundary (21 / 20) 14 = 2 ∧
    coverageBinBoundary (21 / 20) 15 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [coverageBinBoundary, Nat.ceil_eq_iff (by norm_num)] <;> norm_num

/-- With `b = 1.05`, bin `15` is `(2, 3]` and is modelled with `⌈√6⌉ = 3` reads. -/
example : binReadCoverage (21 / 20) 15 = 3 := by
  have h14 : coverageBinBoundary (21 / 20) 14 = 2 := by
    rw [coverageBinBoundary, Nat.ceil_eq_iff (by norm_num)]; norm_num
  have h15 : coverageBinBoundary (21 / 20) 15 = 3 := by
    rw [coverageBinBoundary, Nat.ceil_eq_iff (by norm_num)]; norm_num
  rw [binReadCoverage, representativeCoverage, Nat.ceil_eq_iff (by norm_num),
    show 15 - 1 = 14 from rfl, h14, h15]
  push_cast
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · calc √(2 * 3) ≤ √(3 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 3 := Real.sqrt_sq (by norm_num)

/-- With `b = 2`, a mean coverage of `2` lies in bin `1 = (1, 2]` and in no other bin. -/
example : InCoverageBin 2 1 2 ∧ ¬ InCoverageBin 2 2 2 := by
  have h1 : coverageBinBoundary 2 1 = 2 := by simp [coverageBinBoundary]
  refine ⟨⟨le_rfl, ?_, ?_⟩, fun h => ?_⟩
  · simp
  · simp [h1]
  · obtain ⟨-, h, -⟩ := h
    simp [h1] at h

/-- The bin of a coverage above `1` is unique. -/
example : ∃! i, InCoverageBin (21 / 20) i 100 :=
  existsUnique_inCoverageBin (by norm_num) (by norm_num)

/-! ### The pooled law and the M-step -/

/-- The mixture of `BetaBin(2 c, 2, 2)` and `BetaBin(2 c, 1/2, 1/2)` with equal weights. -/
noncomputable def θ : AIMixture where
  weight := 1 / 2
  shape₁ := 2
  shape₂ := 1 / 2
  weight_nonneg := by norm_num
  weight_le_one := by norm_num
  one_lt_shape₁ := by norm_num
  shape₂_pos := by norm_num
  shape₂_lt_one := by norm_num

/-- `ω₁ BB(2; 2, 2)(1) + ω₂ BB(2; 1/2, 1/2)(1) = 1/2 · 2/5 + 1/2 · 1/4 = 13/40`. -/
example : pooledMass θ 1 1 = 13 / 40 := by
  norm_num [pooledMass, θ, betaBinomialPMF, ascPochhammer_succ_eval, Nat.choose]

example : pooledMass θ 3 2 = pooledMass θ 3 4 := (pooledMass_symm θ (by norm_num)).symm

example : ∑ k ∈ range 7, (k : ℝ) * pooledMass θ 3 k = 3 := by
  simpa using sum_mul_pooledMass θ 3

/-- The moment-matching shape of the variance `3/5` of `BetaBin(2, 2, 2)` is `2`. -/
example : momentMatchingShape 1 (3 / 5) = 2 := by
  norm_num [momentMatchingShape]

example : momentMatchingShape 1 (3 / 5) = 2 :=
  (momentMatchingShape_eq_iff le_rfl (by norm_num : (0 : ℝ) < 2)).mpr (by norm_num)

/-- With `c = 0` reads, no shape matches: the formula gives `-4 v / (8 v) = -1/2` for every
variance `v ≠ 0`, and the junk value `0` at `v = 0`. -/
example (v : ℝ) (hv : v ≠ 0) : momentMatchingShape 0 v = -1 / 2 := by
  simp only [momentMatchingShape, Nat.cast_zero, mul_zero, sub_zero]
  field_simp
  ring

example : momentMatchingShape 0 0 = 0 := by
  simp [momentMatchingShape]

/-- The M-step recovers the shape `2` from the exact law of `BetaBin(6, 2, 2)`. -/
example : mStepShape 3 (range 7) (betaBinomialPMF 6 2 2) (fun k => k) = 2 :=
  mStepShape_betaBinomialPMF (c := 3) (by norm_num) (by norm_num)

/-- A sample of counts weighted by responsibilities: counts `0` and `2` out of `2` reads, each with
responsibility `1`, have weighted variance `1` about `c = 1`, which no shape matches
(`8 · 1 - 4 = 4 ≠ 0`, shape `(4 - 4) / 4 = 0`). -/
example : mStepShape 1 (range 2) (fun _ => 1) (fun n => 2 * n) = 0 := by
  norm_num [mStepShape, momentMatchingShape, sum_range_succ]

/-! ### The expected law -/

/-- `BetaBin(·, 2, 2)` alone. -/
noncomputable def θ₀ : AIMixture where
  weight := 1
  shape₁ := 2
  shape₂ := 1 / 2
  weight_nonneg := by norm_num
  weight_le_one := by norm_num
  one_lt_shape₁ := by norm_num
  shape₂_pos := by norm_num
  shape₂_lt_one := by norm_num

/-- The pooled law of `4` reads under `θ₀`. -/
theorem pooledMass_θ₀ :
    pooledMass θ₀ 2 0 = 1 / 7 ∧ pooledMass θ₀ 2 1 = 8 / 35 ∧ pooledMass θ₀ 2 2 = 9 / 35 ∧
      pooledMass θ₀ 2 3 = 8 / 35 ∧ pooledMass θ₀ 2 4 = 1 / 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [pooledMass, θ₀, betaBinomialPMF, ascPochhammer_succ_eval, Nat.choose]

/-- The replicate-pair law of `θ₀` with two reads per replicate. -/
theorem replicatePairMass_θ₀ :
    replicatePairMass θ₀ 2 0 0 = 1 / 7 ∧ replicatePairMass θ₀ 2 0 1 = 4 / 35 ∧
      replicatePairMass θ₀ 2 0 2 = 3 / 70 ∧ replicatePairMass θ₀ 2 1 0 = 4 / 35 ∧
      replicatePairMass θ₀ 2 1 1 = 6 / 35 ∧ replicatePairMass θ₀ 2 1 2 = 4 / 35 ∧
      replicatePairMass θ₀ 2 2 0 = 3 / 70 ∧ replicatePairMass θ₀ 2 2 1 = 4 / 35 ∧
      replicatePairMass θ₀ 2 2 2 = 1 / 7 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := pooledMass_θ₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [replicatePairMass] <;> norm_num [h0, h1, h2, h3, h4, Nat.choose]

/-- The simulated law: with `p ~ Beta(2, 2)` and two independent `Bin(2, p)` counts, both counts
are `0` with probability `∫ (1 - p) ^ 4 dBeta(2, 2)(p) = 1/7`. -/
example : (1 : ℝ) * ∫ p, ((2 : ℕ).choose 0 * p ^ 0 * (1 - p) ^ (2 - 0)) *
        ((2 : ℕ).choose 0 * p ^ 0 * (1 - p) ^ (2 - 0)) ∂betaMeasure 2 2 +
      (1 - 1) * ∫ p, ((2 : ℕ).choose 0 * p ^ 0 * (1 - p) ^ (2 - 0)) *
        ((2 : ℕ).choose 0 * p ^ 0 * (1 - p) ^ (2 - 0)) ∂betaMeasure (1 / 2) (1 / 2) = 1 / 7 := by
  have h := replicatePairMass_eq_integral θ₀ 2 0 0
  simp only [θ₀] at h
  rw [← h]
  exact replicatePairMass_θ₀.1

/-- The pooled count follows the fitted mixture: `P(j₁ + j₂ = 2) = 3/70 + 6/35 + 3/70 = 9/35`. -/
example : ∑ ij ∈ antidiagonal 2, replicatePairMass θ₀ 2 ij.1 ij.2 = 9 / 35 := by
  rw [sum_antidiagonal_replicatePairMass]
  exact pooledMass_θ₀.2.2.1

/-- The lower `u`-quantile of a probability measure is `x` when `u ≤ μ (-∞, x]` and
`μ (-∞, x) < u`. -/
theorem cdfQuantile_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] {u x : ℝ}
    (hu : u ∈ Set.Ioo 0 1) (h₁ : u ≤ μ.real (Set.Iic x)) (h₂ : μ.real (Set.Iio x) < u) :
    cdfQuantile μ u = x := by
  apply le_antisymm
  · rw [cdfQuantile_le_iff μ hu, cdf_eq_real]
    exact h₁
  · by_contra h
    have hlt := lt_of_not_ge h
    have hmem := cdfQuantile_mem μ hu
    rw [cdf_eq_real] at hmem
    have := measureReal_mono (μ := μ) (Set.Iic_subset_Iio.mpr hlt)
    linarith

/-- The measure of a measurable set under a finite sum of weighted Dirac masses. -/
theorem measureReal_sum_dirac {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (a : ι → ℝ) {t : Set ℝ} (ht : MeasurableSet t) [DecidablePred (· ∈ t)] :
    (∑ i ∈ s, ENNReal.ofReal (w i) • Measure.dirac (a i)).real t =
      ∑ i ∈ s, if a i ∈ t then w i else 0 := by
  rw [measureReal_def, FunLike.coe_sum, Finset.sum_apply, ENNReal.toReal_sum]
  · refine sum_congr rfl fun i hi => ?_
    rw [smul_apply, Measure.dirac_apply' _ ht, smul_eq_mul]
    by_cases h : a i ∈ t
    · simp [h, ENNReal.toReal_ofReal (hw i hi)]
    · simp [h]
  · intro i _
    rw [smul_apply, Measure.dirac_apply' _ ht, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by by_cases h : a i ∈ t <;> simp [h])

/-- The expected law of `ΔAI` for `θ₀` and two reads per replicate, as a table of the nine
pairs. -/
theorem expectedDeltaAILaw_real (t : Set ℝ) (ht : MeasurableSet t) [DecidablePred (· ∈ t)] :
    (expectedDeltaAILaw θ₀ 2).real t =
      (if (0 : ℝ) ∈ t then 16 / 35 else 0) + (if (1 / 2 : ℝ) ∈ t then 16 / 35 else 0) +
        (if (1 : ℝ) ∈ t then 3 / 35 else 0) := by
  obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := replicatePairMass_θ₀
  rw [expectedDeltaAILaw, measureReal_sum_dirac _ _ (fun j _ => replicatePairMass_nonneg _ _ _ _)
    _ ht]
  rw [sum_product]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  norm_num [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  split_ifs <;> norm_num

instance : IsProbabilityMeasure (expectedDeltaAILaw θ₀ 2) :=
  isProbabilityMeasure_expectedDeltaAILaw θ₀ 2

/-- The quantiles of the expected `ΔAI` at `1/5`, `1/2` and `19/20` are `0`, `1/2` and `1`. -/
theorem cdfQuantile_expectedDeltaAILaw :
    cdfQuantile (expectedDeltaAILaw θ₀ 2) (1 / 5) = 0 ∧
      cdfQuantile (expectedDeltaAILaw θ₀ 2) (1 / 2) = 1 / 2 ∧
      cdfQuantile (expectedDeltaAILaw θ₀ 2) (19 / 20) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine cdfQuantile_eq _ (by norm_num) ?_ ?_ <;>
    rw [expectedDeltaAILaw_real _ (by measurability)] <;> norm_num

/-! ### An end-to-end QCC -/

/-- Maternal reads of the four genes in the two replicates. -/
def mat : Fin 2 → Fin 4 → ℕ := ![![1, 2, 0, 2], ![2, 0, 2, 0]]

/-- Paternal reads of the four genes in the two replicates. -/
def pat : Fin 2 → Fin 4 → ℕ := ![![1, 0, 2, 0], ![0, 2, 0, 2]]

/-- Every gene has two reads in each replicate, so mean coverage `2`, in bin `1 = (1, 2]` of
base `2`. -/
theorem binGenes_eq : binGenes 2 1 mat pat 0 1 = univ := by
  rw [eq_univ_iff_forall]
  intro g
  fin_cases g <;>
    norm_num [binGenes, InCoverageBin, coverageBinBoundary, mat, pat]

/-- No gene lies in bin `2 = (2, 4]` of base `2`. -/
theorem binGenes_two : binGenes 2 2 mat pat 0 1 = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro g
  fin_cases g <;>
    norm_num [binGenes, InCoverageBin, coverageBinBoundary, mat, pat]

/-- The observed `ΔAI` is `1/2` for gene `0` and `1` for the other three. -/
theorem observedDeltaAILaw_real (t : Set ℝ) (ht : MeasurableSet t) [DecidablePred (· ∈ t)] :
    (observedDeltaAILaw 2 1 mat pat 0 1).real t =
      (if (1 / 2 : ℝ) ∈ t then 1 / 4 else 0) + (if (1 : ℝ) ∈ t then 3 / 4 else 0) := by
  have hlaw : observedDeltaAILaw 2 1 mat pat 0 1 =
      ∑ g : Fin 4, ENNReal.ofReal (1 / 4) • Measure.dirac
        |allelicImbalance (mat 0 g) (pat 0 g) - allelicImbalance (mat 1 g) (pat 1 g)| := by
    rw [observedDeltaAILaw, binGenes_eq, smul_sum, card_univ, Fintype.card_fin]
    congr 1
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hlaw, measureReal_sum_dirac _ _ (fun _ _ => by norm_num) _ ht, Fin.sum_univ_four]
  norm_num [allelicImbalance, mat, pat]
  split_ifs <;> norm_num

instance : IsProbabilityMeasure (observedDeltaAILaw 2 1 mat pat 0 1) :=
  isProbabilityMeasure_observedDeltaAILaw (by rw [binGenes_eq]; exact univ_nonempty)

/-- The observed quantiles at `1/5`, `1/2` and `19/20` are `1/2`, `1` and `1`. -/
theorem cdfQuantile_observedDeltaAILaw :
    cdfQuantile (observedDeltaAILaw 2 1 mat pat 0 1) (1 / 5) = 1 / 2 ∧
      cdfQuantile (observedDeltaAILaw 2 1 mat pat 0 1) (1 / 2) = 1 ∧
      cdfQuantile (observedDeltaAILaw 2 1 mat pat 0 1) (19 / 20) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine cdfQuantile_eq _ (by norm_num) ?_ ?_ <;>
    rw [observedDeltaAILaw_real _ (by measurability)] <;> norm_num

/-- Bin `1` of base `2` is modelled with `⌈√2⌉ = 2` reads per replicate. -/
theorem binReadCoverage_two_one : binReadCoverage 2 1 = 2 := by
  rw [binReadCoverage, representativeCoverage, Nat.ceil_eq_iff (by norm_num)]
  norm_num [coverageBinBoundary]
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- The quantile levels of the example. -/
noncomputable def levels : Finset ℝ := {1 / 5, 1 / 2, 19 / 20}

/-- The QCC of the two replicates: the ratio at `1/5` is undefined and left out, those at `1/2`
and `19/20` are `2` and `1`, so the QCC is `3/2`. Bin `2`, with no genes, contributes nothing. -/
theorem pairQualityCorrectionConstant_example :
    pairQualityCorrectionConstant 2 {1, 2} levels (fun _ => θ₀) mat pat 0 1 = 3 / 2 := by
  obtain ⟨e₁, e₂, e₃⟩ := cdfQuantile_expectedDeltaAILaw
  obtain ⟨o₁, o₂, o₃⟩ := cdfQuantile_observedDeltaAILaw
  have hbins : ({1, 2} : Finset ℕ).filter (fun i => (binGenes 2 i mat pat 0 1).Nonempty) = {1} := by
    ext i
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h | h, hne⟩
      · exact h
      · subst h
        rw [binGenes_two] at hne
        exact absurd hne not_nonempty_empty
    · rintro rfl
      exact ⟨Or.inl rfl, by rw [binGenes_eq]; exact univ_nonempty⟩
  have hS : (({1} : Finset ℕ) ×ˢ levels).filter
      (fun iq => cdfQuantile (expectedDeltaAILaw θ₀ (binReadCoverage 2 iq.1)) iq.2 ≠ 0) =
        {(1, 1 / 2), (1, 19 / 20)} := by
    ext ⟨i, q⟩
    simp only [levels, mem_filter, mem_product, mem_singleton, mem_insert, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨rfl, hq⟩, hne⟩
      rw [binReadCoverage_two_one] at hne
      rcases hq with rfl | rfl | rfl
      · exact absurd e₁ hne
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        refine ⟨⟨rfl, by norm_num⟩, ?_⟩ <;> rw [binReadCoverage_two_one] <;> norm_num [e₂, e₃]
  unfold pairQualityCorrectionConstant quantileRatioFit
  rw [hbins, hS, expect_eq_sum_div_card, sum_pair (by norm_num), card_pair (by norm_num)]
  simp only [binReadCoverage_two_one, e₂, e₃, o₂, o₃]
  norm_num

/-- With two replicates the QCC is that of the pair, with the pair's bins. -/
example : qualityCorrectionConstant 2 (fun _ _ => {1, 2}) levels (fun _ _ _ => θ₀) mat pat =
    3 / 2 := by
  rw [qualityCorrectionConstant_two]
  exact pairQualityCorrectionConstant_example

/-- A gene of coverage `9` has effective coverage `9 / (3/2) ^ 2 = 4`, and the standard deviation
of its AI is widened by `3/2`. -/
example : effectiveCoverage 9 (3 / 2) = 4 := by
  norm_num [effectiveCoverage]

example (a : ℝ) : √(a * (1 - a) / effectiveCoverage 9 (3 / 2)) = 3 / 2 * √(a * (1 - a) / 9) := by
  simpa using sqrt_div_effectiveCoverage 9 (by norm_num : (0 : ℝ) ≤ 3 / 2) a

/-! ### More replicates -/

example : (replicatePairs 3).card = 3 := by
  rw [card_replicatePairs]
  rfl

/-- With three replicates the QCC is the mean of the three pairwise QCCs, each with its own bins
and fitted mixtures. -/
example {γ : Type*} [Fintype γ] (b : ℝ) (bins : Fin 3 → Fin 3 → Finset ℕ) (lv : Finset ℝ)
    (fit : Fin 3 → Fin 3 → ℕ → AIMixture) (m p : Fin 3 → γ → ℕ) :
    qualityCorrectionConstant b bins lv fit m p =
      (pairQualityCorrectionConstant b (bins 0 1) lv (fit 0 1) m p 0 1 +
        pairQualityCorrectionConstant b (bins 0 2) lv (fit 0 2) m p 0 2 +
        pairQualityCorrectionConstant b (bins 1 2) lv (fit 1 2) m p 1 2) / 3 := by
  have : replicatePairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
  rw [qualityCorrectionConstant, this, expect_eq_sum_div_card, sum_insert (by decide),
    sum_pair (by decide)]
  norm_num [add_assoc]

/-- With one replicate there is no pair, and the QCC is the junk value `0`. -/
example {γ : Type*} [Fintype γ] (b : ℝ) (bins : Fin 1 → Fin 1 → Finset ℕ) (lv : Finset ℝ)
    (fit : Fin 1 → Fin 1 → ℕ → AIMixture) (m p : Fin 1 → γ → ℕ) :
    qualityCorrectionConstant b bins lv fit m p = 0 :=
  qualityCorrectionConstant_of_lt_two (by norm_num) b bins lv fit m p

/-! ### The fit -/

/-- Observed quantiles twice the expected ones give the constant `2`. -/
example : quantileRatioFit ({0} : Finset ℕ) {1 / 2, 9 / 10} (fun _ q => 2 * q) (fun _ q => q) = 2 :=
  quantileRatioFit_eq_of_forall _ _ _ _ ⟨(0, 1 / 2), by simp⟩ fun _ _ _ _ _ => rfl

/-- With no defined ratio the fit is the junk value `0`. -/
example (Qobs : ℕ → ℝ → ℝ) : quantileRatioFit ({0} : Finset ℕ) {1 / 2} Qobs (fun _ _ => 0) = 0 := by
  simp [quantileRatioFit]

/-- The least-squares property: the fit has no larger squared error on the defined ratios than the
constant `1`. -/
example (Qobs Qexp : ℕ → ℝ → ℝ) :
    ∑ iq ∈ (({0} : Finset ℕ) ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0),
        (Qobs iq.1 iq.2 / Qexp iq.1 iq.2 - quantileRatioFit {0} levels Qobs Qexp) ^ 2 ≤
      ∑ iq ∈ (({0} : Finset ℕ) ×ˢ levels).filter (fun iq => Qexp iq.1 iq.2 ≠ 0),
        (Qobs iq.1 iq.2 / Qexp iq.1 iq.2 - 1) ^ 2 :=
  sum_sq_sub_quantileRatioFit_le _ _ _ _ 1

end DomainsTest.Biology.Omics.AllelicImbalanceQualityCorrection
