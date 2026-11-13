/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Learning.FiniteRisk
public import Cslib.MachineLearning.PACLearning.Defs

@[expose] public section

/-! # Agnostic finite-class ERM: excess-risk bound and PAC restatement -/

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Agnostic finite-class excess-risk bound. The empirical-0-1-risk minimizer over a finite
nonempty hypothesis class exceeds the best class error by more than `2ε` only on a bad set
of product mass at most `2|C|exp(-2mε²)`. -/
theorem agnosticFiniteClass_excessRisk
    {α : Type*} [MeasurableSpace α] {M m : ℕ} [NeZero M] (hm : 0 < m)
    (h : Fin M → (α → Bool))
    (F : Fin M → (α × Bool) → ℝ)
    (hF : ∀ j p, F j p = if h j p.1 ≠ p.2 then (1 : ℝ) else (0 : ℝ))
    (herr : ∀ j, MeasurableSet {p : α × Bool | h j p.1 ≠ p.2})
    (D : Measure (α × Bool)) [IsProbabilityMeasure D]
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin m => D).real
      {S : Fin m → α × Bool |
        (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D} ≤
      2 * (M : ℝ) * Real.exp (-2 * (m : ℝ) * ε ^ 2) := by
  have hf : ∀ j, Measurable (F j) := by
    intro j
    have hEq : F j = {p : α × Bool | h j p.1 ≠ p.2}.indicator 1 := by
      funext p
      rw [hF]
      simp only [Set.indicator, Set.mem_ofPred_eq]
      by_cases hp : h j p.1 ≠ p.2 <;> simp [hp]
    rw [hEq]
    exact measurable_const.indicator (herr j)
  have hbd : ∀ j, ∀ᵐ z ∂D, F j z ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    apply Filter.Eventually.of_forall
    intro z
    rw [hF]
    by_cases hz : h j z.1 ≠ z.2
    · simp [hz]
    · simp [hz]
  have hSub : {S : Fin m → α × Bool |
        (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D} ⊆
      {S : Fin m → α × Bool | ∃ j : Fin M,
        ε ≤ |(m : ℝ)⁻¹ * ∑ i : Fin m, F j (S i) - ∫ z, F j z ∂D|} := by
    intro S hS
    simp only [Set.mem_ofPred_eq] at hS ⊢
    by_contra hCon
    have hGood : S ∉ {S : Fin m → α × Bool | ∃ j : Fin M,
        ε ≤ |(m : ℝ)⁻¹ * ∑ i : Fin m, F j (S i) - ∫ z, F j z ∂D|} := hCon
    have hLe := erm_populationRisk_le_best_plus_two D F S hGood
    linarith
  calc (Measure.pi fun _ : Fin m => D).real
        {S : Fin m → α × Bool |
          (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D}
      ≤ (Measure.pi fun _ : Fin m => D).real
        {S : Fin m → α × Bool | ∃ j : Fin M,
          ε ≤ |(m : ℝ)⁻¹ * ∑ i : Fin m, F j (S i) - ∫ z, F j z ∂D|} :=
        measureReal_mono hSub (measure_ne_top _ _)
    _ ≤ 2 * (M : ℝ) * Real.exp (-2 * (m : ℝ) * ε ^ 2) :=
        measure_exists_abs_empirical_sub_integral_ge_le D hm F hf hbd hε

/-- Agnostic finite-class PAC restatement. Under the log sample bound the ERM rule is a PAC
learner for the class range, uniformly over all data laws, with no realizability assumed. -/
theorem agnosticFiniteClass_isPACLearner
    {α : Type*} [MeasurableSpace α] {M m : ℕ} [NeZero M] (hm : 0 < m)
    (h : Fin M → (α → Bool))
    (F : Fin M → (α × Bool) → ℝ)
    (hF : ∀ j p, F j p = if h j p.1 ≠ p.2 then (1 : ℝ) else (0 : ℝ))
    (herr : ∀ j, MeasurableSet {p : α × Bool | h j p.1 ≠ p.2})
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm_log : Real.log (2 * (M : ℝ) / δ) / (2 * ε ^ 2) ≤ (m : ℝ))
    (ε' δ' : Set.Ioo (0 : ℝ≥0) 1)
    (hε' : (ε'.val : ℝ) = 2 * ε) (hδ' : (δ'.val : ℝ) = δ) :
    IsPACLearnerFor m ε' δ' (Set.range h) Set.univ := by
  have _ : ε < 1 / 2 := hε1
  have _ : δ < 1 := hδ1
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  have h2Mpos : (0 : ℝ) < 2 * (M : ℝ) := by linarith
  have hdivpos : (0 : ℝ) < 2 * (M : ℝ) / δ := div_pos h2Mpos hδ0
  have hdenompos : (0 : ℝ) < 2 * ε ^ 2 := by positivity
  have hlog_le : Real.log (2 * (M : ℝ) / δ) ≤ (m : ℝ) * (2 * ε ^ 2) := by
    have h := (div_le_iff₀ hdenompos).mp hm_log
    linarith
  have hlog_le2 : Real.log (2 * (M : ℝ) / δ) ≤ 2 * (m : ℝ) * ε ^ 2 := by linarith
  have hneg_le : -2 * (m : ℝ) * ε ^ 2 ≤ -Real.log (2 * (M : ℝ) / δ) := by linarith
  have hexp_le : Real.exp (-2 * (m : ℝ) * ε ^ 2)
      ≤ Real.exp (-Real.log (2 * (M : ℝ) / δ)) :=
    Real.exp_le_exp.mpr hneg_le
  have hexp_eq : Real.exp (-Real.log (2 * (M : ℝ) / δ)) = δ / (2 * (M : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log hdivpos, inv_div]
  rw [hexp_eq] at hexp_le
  have h2Mne : (2 : ℝ) * (M : ℝ) ≠ 0 := ne_of_gt h2Mpos
  have hδ : 2 * (M : ℝ) * Real.exp (-2 * (m : ℝ) * ε ^ 2) ≤ δ := by
    calc 2 * (M : ℝ) * Real.exp (-2 * (m : ℝ) * ε ^ 2)
        ≤ 2 * (M : ℝ) * (δ / (2 * (M : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp_le (le_of_lt h2Mpos)
      _ = δ := by field_simp
  have hε : (0 : ℝ) ≤ ε := le_of_lt hε0
  have h2εNonneg : (0 : ℝ) ≤ 2 * ε := by linarith
  refine ⟨fun S => h (ermIdx F S), ?_⟩
  intro D _ _
  have hExcess := agnosticFiniteClass_excessRisk hm h F hF herr D hε
  have hRealLe : (Measure.pi fun _ : Fin m => D).real
      {S : Fin m → α × Bool |
        (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D} ≤ δ :=
    le_trans hExcess hδ
  have hFEq : ∀ j, F j = {p : α × Bool | h j p.1 ≠ p.2}.indicator 1 := by
    intro j
    funext p
    rw [hF]
    simp only [Set.indicator, Set.mem_ofPred_eq]
    by_cases hp : h j p.1 ≠ p.2 <;> simp [hp]
  have hErrEq : ∀ j, error D (h j) = ENNReal.ofReal (∫ z, F j z ∂D) := by
    intro j
    unfold error
    rw [hFEq j, integral_indicator_one (herr j), measureReal_def]
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hOptEq : optimalError D (Set.range h) = ⨅ j, error D (h j) := by
    unfold optimalError
    rw [iInf_range]
  have hIntNonneg : ∀ j, (0 : ℝ) ≤ ∫ z, F j z ∂D := by
    intro j
    apply integral_nonneg
    intro p
    rw [hF]
    by_cases hp : h j p.1 ≠ p.2 <;> simp [hp]
  have hInfNonneg : (0 : ℝ) ≤ ⨅ j, ∫ z, F j z ∂D := by
    have hneM : Nonempty (Fin M) := Fin.pos_iff_nonempty.mp (NeZero.pos M)
    exact @le_ciInf _ _ _ hneM _ _ (fun j => hIntNonneg j)
  have hbdd : BddBelow (Set.range (fun j : Fin M => ∫ z, F j z ∂D)) :=
    Finite.bddBelow_range _
  have hOfRealInfLe : ENNReal.ofReal (⨅ j, ∫ z, F j z ∂D)
      ≤ ⨅ j, ENNReal.ofReal (∫ z, F j z ∂D) := by
    apply le_iInf
    intro j
    apply ENNReal.ofReal_le_ofReal
    exact ciInf_le hbdd j
  have hEpsBridge : ENNReal.ofReal (2 * ε) = (ε'.val : ℝ≥0∞) := by
    rw [← hε']
    exact ENNReal.ofReal_coe_nnreal
  have hDeltaBridge : ENNReal.ofReal δ = (δ'.val : ℝ≥0∞) := by
    rw [← hδ']
    exact ENNReal.ofReal_coe_nnreal
  have hSubFail : {S : LabeledSample α Bool m |
        optimalError D (Set.range h) + ↑ε'.val < error D (h (ermIdx F S))} ⊆
      {S : Fin m → α × Bool |
        (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D} := by
    intro S hFail
    simp only [Set.mem_ofPred_eq] at hFail ⊢
    rw [hOptEq] at hFail
    have hErrErm : error D (h (ermIdx F S))
        = ENNReal.ofReal (∫ z, F (ermIdx F S) z ∂D) := hErrEq _
    rw [hErrErm] at hFail
    have hInfEq : (⨅ j, error D (h j)) = ⨅ j, ENNReal.ofReal (∫ z, F j z ∂D) := by
      congr 1
      funext j
      exact hErrEq j
    rw [hInfEq] at hFail
    rw [← hEpsBridge] at hFail
    by_contra hCon
    have hRealLe' : ∫ z, F (ermIdx F S) z ∂D ≤ (⨅ j, ∫ z, F j z ∂D) + 2 * ε :=
      le_of_not_gt hCon
    have h1 : ENNReal.ofReal (∫ z, F (ermIdx F S) z ∂D)
        ≤ ENNReal.ofReal ((⨅ j, ∫ z, F j z ∂D) + 2 * ε) :=
      ENNReal.ofReal_le_ofReal hRealLe'
    have h2 : ENNReal.ofReal ((⨅ j, ∫ z, F j z ∂D) + 2 * ε)
        = ENNReal.ofReal (⨅ j, ∫ z, F j z ∂D) + ENNReal.ofReal (2 * ε) :=
      ENNReal.ofReal_add hInfNonneg h2εNonneg
    rw [h2] at h1
    have h3 : ENNReal.ofReal (⨅ j, ∫ z, F j z ∂D) + ENNReal.ofReal (2 * ε)
        ≤ (⨅ j, ENNReal.ofReal (∫ z, F j z ∂D)) + ENNReal.ofReal (2 * ε) :=
      add_le_add_left hOfRealInfLe _
    have h4 : ENNReal.ofReal (∫ z, F (ermIdx F S) z ∂D)
        ≤ (⨅ j, ENNReal.ofReal (∫ z, F j z ∂D)) + ENNReal.ofReal (2 * ε) :=
      le_trans h1 h3
    exact not_lt_of_ge h4 hFail
  have hPiNeTop : (Measure.pi fun _ : Fin m => D)
      {S : Fin m → α × Bool |
        (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D} ≠ ⊤ :=
    measure_ne_top _ _
  have hENNReal : (Measure.pi fun _ : Fin m => D)
      {S : Fin m → α × Bool |
        (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D}
      ≤ (δ'.val : ℝ≥0∞) := by
    have h1 : (Measure.pi fun _ : Fin m => D)
        {S : Fin m → α × Bool |
          (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D}
        = ENNReal.ofReal ((Measure.pi fun _ : Fin m => D).real
          {S : Fin m → α × Bool |
            (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D}) := by
      rw [measureReal_def, ENNReal.ofReal_toReal hPiNeTop]
    rw [h1, ← hDeltaBridge]
    exact ENNReal.ofReal_le_ofReal hRealLe
  calc (Measure.pi fun _ : Fin m => D)
        {S : LabeledSample α Bool m |
          optimalError D (Set.range h) + ↑ε'.val < error D (h (ermIdx F S))}
      ≤ (Measure.pi fun _ : Fin m => D)
        {S : Fin m → α × Bool |
          (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D} :=
        measure_mono hSubFail
    _ ≤ (δ'.val : ℝ≥0∞) := hENNReal

end Cslib.MachineLearning.PACLearning
