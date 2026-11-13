/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.Scales
public import MathlibExt.Probability.Statistics.Measurement.AffineLaws
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tests for ordinal scales and affine laws

Checks ranks, order statistics and medians via the public API, affine laws
for means and variances, guarded ratio invariance, and the group-mean
reversal consequence.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement

open MathlibExt.Probability.Statistics.Measurement
open scoped BigOperators ENNReal

/-- Tied T1 sample `![1, 0, 1]`: subject 1 below, 0 and 2 tied. -/
def t1Sample : Fin (2 + 1) → ℕ := ![1, 0, 1]

/-- T1 tied ranks agree with values via the public iff. -/
theorem t1_tied_ranks_via_iff :
    sampleRank t1Sample 1 < sampleRank t1Sample 0 ∧
    sampleRank t1Sample 1 < sampleRank t1Sample 2 ∧
    ¬(sampleRank t1Sample 0 < sampleRank t1Sample 2) ∧
    ¬(sampleRank t1Sample 2 < sampleRank t1Sample 0) ∧
    sampleRank t1Sample 0 = sampleRank t1Sample 2 := by
  have h0 : t1Sample 0 = 1 := by simp [t1Sample]
  have h1 : t1Sample 1 = 0 := by simp [t1Sample]
  have h2 : t1Sample 2 = 1 := by simp [t1Sample]
  have hx10 : t1Sample 1 < t1Sample 0 := by rw [h1, h0]; decide
  have hx12 : t1Sample 1 < t1Sample 2 := by rw [h1, h2]; decide
  have hx02 : ¬(t1Sample 0 < t1Sample 2) := by rw [h0, h2]; decide
  have hx20 : ¬(t1Sample 2 < t1Sample 0) := by rw [h2, h0]; decide
  have hr10 : sampleRank t1Sample 1 < sampleRank t1Sample 0 :=
    (sampleRank_lt_sampleRank_iff t1Sample 1 0).mpr hx10
  have hr12 : sampleRank t1Sample 1 < sampleRank t1Sample 2 :=
    (sampleRank_lt_sampleRank_iff t1Sample 1 2).mpr hx12
  have hr02 : ¬(sampleRank t1Sample 0 < sampleRank t1Sample 2) := by
    rw [sampleRank_lt_sampleRank_iff]
    exact hx02
  have hr20 : ¬(sampleRank t1Sample 2 < sampleRank t1Sample 0) := by
    rw [sampleRank_lt_sampleRank_iff]
    exact hx20
  have heq : sampleRank t1Sample 0 = sampleRank t1Sample 2 :=
    le_antisymm (le_of_not_gt hr20) (le_of_not_gt hr02)
  exact ⟨hr10, hr12, hr02, hr20, heq⟩

/-- Order statistics are monotone on the T1 sample. -/
theorem t1_orderStatistics_monotone :
    orderStatistic t1Sample 0 ≤ orderStatistic t1Sample 2 := by
  have hmono := monotone_orderStatistic t1Sample
  have hle : (0 : Fin (2 + 1)) ≤ 2 := by decide
  exact hmono hle

/-- Ranks are invariant under adding a constant. -/
theorem t1_rank_invariant_under_add :
    ∀ i, sampleRank ((fun n : ℕ => n + 10) ∘ t1Sample) i =
      sampleRank t1Sample i := by
  intro i
  apply sampleRank_comp_of_strictMono
  intro a b hab
  dsimp only
  omega

/-- A constant (hence non-strictly-monotone) map collapses distinct ranks:
subjects `1` and `0` are strictly ranked in `t1Sample` by
`sampleRank_lt_sampleRank_iff`, yet share one rank after recoding. -/
theorem t1_constant_map_collapses_ranks :
    sampleRank t1Sample 1 < sampleRank t1Sample 0 ∧
    sampleRank ((fun _ : ℕ => 5) ∘ t1Sample) 1 =
      sampleRank ((fun _ : ℕ => 5) ∘ t1Sample) 0 := by
  have hx : t1Sample 1 < t1Sample 0 := by simp [t1Sample]
  constructor
  · exact (sampleRank_lt_sampleRank_iff t1Sample 1 0).mpr hx
  · simp [sampleRank]

/-- Order statistics commute with doubling. -/
theorem t1_orderStatistic_commutes :
    ∀ k, orderStatistic ((fun n : ℕ => n * 2) ∘ t1Sample) k =
      (fun n : ℕ => n * 2) (orderStatistic t1Sample k) := by
  intro k
  apply orderStatistic_comp_of_monotone
  intro a b hab
  dsimp only
  omega

/-- Both medians commute with doubling. -/
theorem t1_medians_commute :
    lowerMedian ((fun n : ℕ => n * 2) ∘ t1Sample) =
      (fun n : ℕ => n * 2) (lowerMedian t1Sample) ∧
    upperMedian ((fun n : ℕ => n * 2) ∘ t1Sample) =
      (fun n : ℕ => n * 2) (upperMedian t1Sample) := by
  have hmono : Monotone (fun n : ℕ => n * 2) := by
    intro a b hab
    dsimp only
    omega
  constructor
  · exact lowerMedian_comp_of_monotone hmono
  · exact upperMedian_comp_of_monotone hmono

/-- Four-point sample `fun i => i` for the averaging counterexample. -/
def avgMidSample : Fin 4 → ℝ := fun i => (i.val : ℝ)

/-- Averaging the two middle values does not commute with a strictly
increasing map: cubing the average of the two middle order statistics
differs from averaging the order statistics after cubing. -/
theorem averaged_middle_not_invariant :
    StrictMono (fun t : ℝ => t ^ 3) ∧
    (fun t : ℝ => t ^ 3) ((orderStatistic avgMidSample ⟨1, by decide⟩ +
      orderStatistic avgMidSample ⟨2, by decide⟩) / 2) ≠
    (orderStatistic ((fun t : ℝ => t ^ 3) ∘ avgMidSample) ⟨1, by decide⟩ +
      orderStatistic ((fun t : ℝ => t ^ 3) ∘ avgMidSample) ⟨2, by decide⟩) / 2 := by
  have hmono3 : StrictMono (fun t : ℝ => t ^ 3) := by
    have h3 : Odd (3 : ℕ) := ⟨1, rfl⟩
    exact h3.strictMono_pow
  have hmono : Monotone (avgMidSample ∘ ⇑(Equiv.refl (Fin 4))) :=
    fun _ _ hij => Nat.cast_le.mpr hij
  have hsort : avgMidSample ∘ Tuple.sort avgMidSample = avgMidSample := by
    have h := (Tuple.comp_sort_eq_comp_iff_monotone (σ := Equiv.refl (Fin 4))).mpr hmono
    simpa using h.symm
  have v1 : orderStatistic avgMidSample ⟨1, by decide⟩ = 1 := by
    simpa [orderStatistic, avgMidSample] using congrFun hsort ⟨1, by decide⟩
  have v2 : orderStatistic avgMidSample ⟨2, by decide⟩ = 2 := by
    simpa [orderStatistic, avgMidSample] using congrFun hsort ⟨2, by decide⟩
  constructor
  · exact hmono3
  · rw [orderStatistic_comp_of_monotone hmono3.monotone,
      orderStatistic_comp_of_monotone hmono3.monotone, v1, v2]
    show ((1 + 2) / 2 : ℝ) ^ 3 ≠ ((1 : ℝ) ^ 3 + (2 : ℝ) ^ 3) / 2
    norm_num

/-- Mean affine law applies to a concrete slope and intercept. -/
theorem t2_mean_affine_applies {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MeasureTheory.Integrable X μ) :
    ∫ ω, (2 * X ω + 3) ∂μ = 2 * ∫ ω, X ω ∂μ + 3 :=
  MeasureTheory.integral_const_mul_add_const hX

/-- Variance affine law applies to a concrete slope and intercept. -/
theorem t2_variance_affine_applies {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MeasureTheory.AEStronglyMeasurable X μ) :
    ProbabilityTheory.variance (fun ω => 2 * X ω + 3) μ =
      2 ^ 2 * ProbabilityTheory.variance X μ :=
  ProbabilityTheory.variance_const_mul_add_const hX

/-- Two-point Celsius sample `![0, 20]`. -/
def celsiusTemps : Fin 2 → ℝ := ![0, 20]

/-- Fair-coin PMF on `Fin 2`. -/
noncomputable def fairFin2 : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => (1/2 : ℝ≥0∞)) (by
    rw [Fin.sum_univ_two]
    exact ENNReal.add_halves 1)

/-- Each outcome of the fair coin has probability `1 / 2`. -/
theorem fairFin2_apply (i : Fin 2) : (fairFin2 i).toReal = 1 / 2 := by
  simp [fairFin2]

/-- Mean of the two-point Celsius law is `10`, via `PMF.integral_eq_sum`. -/
theorem celsius_mean : ∫ a, celsiusTemps a ∂fairFin2.toMeasure = 10 := by
  have v0 : celsiusTemps 0 = 0 := by simp [celsiusTemps]
  have v1 : celsiusTemps 1 = 20 := by simp [celsiusTemps]
  rw [PMF.integral_eq_sum, Fin.sum_univ_two, fairFin2_apply 0, fairFin2_apply 1,
    v0, v1]
  norm_num

/-- Variance of the two-point Celsius law is `100`, via `variance_eq_integral`. -/
theorem celsius_variance :
    ProbabilityTheory.variance celsiusTemps fairFin2.toMeasure = 100 := by
  have hmeas : AEMeasurable celsiusTemps fairFin2.toMeasure :=
    (measurable_of_finite celsiusTemps).aemeasurable
  rw [ProbabilityTheory.variance_eq_integral hmeas, celsius_mean, PMF.integral_eq_sum,
    Fin.sum_univ_two]
  have v0 : celsiusTemps 0 = 0 := by simp [celsiusTemps]
  have v1 : celsiusTemps 1 = 20 := by simp [celsiusTemps]
  rw [fairFin2_apply 0, fairFin2_apply 1, v0, v1]
  norm_num

/-- Fahrenheit mean on the two-point law: `9 / 5 * 10 + 32 = 50`. -/
theorem fahrenheit_mean :
    ∫ a, (9/5 * celsiusTemps a + 32) ∂fairFin2.toMeasure = 50 := by
  have hX : MeasureTheory.Integrable celsiusTemps fairFin2.toMeasure :=
    MeasureTheory.Integrable.of_finite
  have h := MeasureTheory.integral_const_mul_add_const (a := (9/5 : ℝ)) (b := (32 : ℝ)) hX
  rw [celsius_mean] at h
  norm_num at h
  exact h

/-- Fahrenheit variance on the two-point law: `(9 / 5) ^ 2 * 100 = 324`. -/
theorem fahrenheit_variance :
    ProbabilityTheory.variance (fun a => 9/5 * celsiusTemps a + 32)
      fairFin2.toMeasure = 324 := by
  have haes : MeasureTheory.AEStronglyMeasurable celsiusTemps fairFin2.toMeasure :=
    (measurable_of_finite celsiusTemps).aestronglyMeasurable
  have h := ProbabilityTheory.variance_const_mul_add_const (a := (9/5 : ℝ)) (b := (32 : ℝ)) haes
  rw [celsius_variance] at h
  norm_num at h
  exact h

/-- Fahrenheit changes the ratio: `68 / 50 ≠ 2` on admissible inputs. -/
theorem t7_fahrenheit_ratio :
    ((9/5 : ℝ) * 20 + 32) / ((9/5) * 10 + 32) ≠ (20 : ℝ) / 10 := by
  norm_num

/-- Guarded ratio invariance fails for Fahrenheit (`b ≠ 0`). -/
theorem t7_guarded_universal_fails :
    ¬∀ x y : ℝ, y ≠ 0 → (9/5 : ℝ) * y + 32 ≠ 0 →
      ((9/5) * x + 32) / ((9/5) * y + 32) = x / y := by
  have ha : (9/5 : ℝ) ≠ 0 := by norm_num
  have hiff := forall_affine_div_affine_eq_div_iff (b := (32 : ℝ)) ha
  have hb : (32 : ℝ) ≠ 0 := by norm_num
  intro hall
  have h32 : (32 : ℝ) = 0 := hiff.mp hall
  exact hb h32

/-- Guarded ratio invariance holds for similarity maps (`b = 0`). -/
theorem t7_similarity_guarded_holds :
    ∀ x y : ℝ, y ≠ 0 → (2 : ℝ) * y + 0 ≠ 0 →
      (2 * x + 0) / (2 * y + 0) = x / y := by
  have ha : (2 : ℝ) ≠ 0 := by norm_num
  have hiff := forall_affine_div_affine_eq_div_iff (b := (0 : ℝ)) ha
  exact hiff.mpr rfl

/-- Ratios of differences are invariant on a concrete example. -/
theorem t8_ratio_diff_example :
    ((2 : ℝ) * 5 + 1 - (2 * 3 + 1)) / (2 * 7 + 1 - (2 * 4 + 1)) =
    (5 - 3) / (7 - 4) :=
  affine_sub_div_affine_sub (by norm_num) 5 3 7 4 (by norm_num)

/-- Zero slope collapses a nonzero difference, without division. -/
theorem t8_zero_slope_collapses_difference :
    ((0 : ℝ) * 3 + 5 - ((0 : ℝ) * 1 + 5)) = 0 ∧ (3 : ℝ) - 1 = 2 := by
  constructor
  · ring
  · norm_num

/-- A constant map is not strictly monotone. -/
theorem t8_zero_slope_not_strictMono :
    ¬StrictMono (fun _ : ℝ => (5 : ℝ)) := by
  intro h
  have h01 : (5 : ℝ) < 5 := h (show (0 : ℝ) < 1 by norm_num)
  exact lt_irrefl 5 h01

/-- The reversal witness yields a strictly monotone recoding that preserves
all ranks yet reverses the group-mean comparison. -/
theorem t12_groupMeans_differ :
    ∃ (f : ℝ → ℝ) (x : Fin 4 → ℝ) (A B : Finset (Fin 4)),
      StrictMono f ∧
      (∀ i, sampleRank (f ∘ x) i = sampleRank x i) ∧
      (𝔼 i ∈ B, x i < 𝔼 i ∈ A, x i) ∧
      (𝔼 i ∈ A, f (x i) < 𝔼 i ∈ B, f (x i)) := by
  obtain ⟨f, x, A, B, hf, _, _, _, hrank, hlt1, hlt2⟩ :=
    exists_strictMono_reverses_groupMean
  exact ⟨f, x, A, B, hf, hrank, hlt1, hlt2⟩

/-- The reversal witness values pin down: recoding values, both group means
before and after recoding, and all four competition ranks. -/
theorem t12_witness_values :
    groupMeanRecode 0 = 0 ∧ groupMeanRecode 1 = 2 ∧ groupMeanRecode 3 = 3 ∧
    (𝔼 i ∈ groupMeanA, groupMeanX i = 3 / 2) ∧
    (𝔼 i ∈ groupMeanB, groupMeanX i = 1) ∧
    (𝔼 i ∈ groupMeanA, groupMeanRecode (groupMeanX i) = 3 / 2) ∧
    (𝔼 i ∈ groupMeanB, groupMeanRecode (groupMeanX i) = 2) ∧
    (sampleRank groupMeanX 0 = 1 ∧ sampleRank groupMeanX 1 = 4 ∧
      sampleRank groupMeanX 2 = 2 ∧ sampleRank groupMeanX 3 = 2) := by
  exact ⟨groupMeanRecode_zero, groupMeanRecode_one, groupMeanRecode_three,
    groupMean_meanA, groupMean_meanB, groupMean_recodeMeanA, groupMean_recodeMeanB,
    groupMean_ranks⟩

end MathlibExtTest.Probability.Statistics.Measurement
