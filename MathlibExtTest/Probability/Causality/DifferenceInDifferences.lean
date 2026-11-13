/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.DifferenceInDifferences
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Count

/-!
# Difference-in-differences checks

Finite coin checks plus counting-measure probes for the narrowed
treated-cell integrability claim and the no-anticipation requirement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Causality

namespace MathlibExtTest.Probability.Causality.DifferenceInDifferences

/-- Outcome with value `a` on `true` and `b` on `false`. -/
def g (a b : ℝ) : Bool → ℝ := fun ω => if ω then a else b

/-- A fair coin. -/
noncomputable def coin : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

/-- Each singleton has coin probability `2⁻¹`. -/
private theorem coin_apply_singleton (b : Bool) : coin {b} = 2⁻¹ := by
  simp only [coin, Measure.smul_apply, Measure.add_apply]
  cases b <;> simp

/-- The fair coin is a probability measure. -/
instance : IsProbabilityMeasure coin := by
  constructor
  have huniv : (Set.univ : Set Bool) = {true} ∪ {false} := by
    ext b
    cases b <;> simp
  rw [huniv, measure_union (by simp) (by simp),
    coin_apply_singleton, coin_apply_singleton]
  have h2 : (2 : ENNReal) ≠ 0 := by simp
  have ht : (2 : ENNReal) ≠ ⊤ := by simp
  have hsum : (2⁻¹ : ENNReal) + 2⁻¹ = 2 * 2⁻¹ := (two_mul _).symm
  rw [hsum, ENNReal.mul_inv_cancel h2 ht]

/-- `(2 : ENNReal)` is nonzero. -/
private theorem enn_two_ne_zero : (2 : ENNReal) ≠ 0 := by simp

/-- `(2 : ENNReal)` is finite. -/
private theorem enn_two_ne_top : (2 : ENNReal) ≠ ⊤ := by simp

/-- `(2⁻¹ : ENNReal)` is nonzero. -/
private theorem enn_inv_two_ne_zero : (2⁻¹ : ENNReal) ≠ 0 :=
  ENNReal.inv_ne_zero.mpr enn_two_ne_top

/-- `(2⁻¹ : ENNReal)` is finite. -/
private theorem enn_inv_two_ne_top : (2⁻¹ : ENNReal) ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr enn_two_ne_zero

/-- Conditioning the coin on `{true}` gives `dirac true`. -/
private theorem coin_cond_true : coin[|{true}] = Measure.dirac true := by
  ext s
  simp only [ProbabilityTheory.cond, coin, Measure.smul_apply,
    Measure.add_apply]
  by_cases h : (true : Bool) ∈ s
  · simp [h, ENNReal.mul_inv_cancel enn_two_ne_zero enn_two_ne_top]
  · simp [h]

/-- Conditioning the coin on `{false}` gives `dirac false`. -/
private theorem coin_cond_false : coin[|{false}] = Measure.dirac false := by
  ext s
  simp only [ProbabilityTheory.cond, coin, Measure.smul_apply,
    Measure.add_apply]
  by_cases h : (false : Bool) ∈ s
  · simp [h, ENNReal.mul_inv_cancel enn_two_ne_zero enn_two_ne_top]
  · simp [h]

/-- The complement of `{true}` in `Bool` is `{false}`. -/
private theorem compl_true : ({true} : Set Bool)ᶜ = {false} := by
  ext b
  cases b <;> simp

/-- Observed outcome on the treated unit equals the treated path. -/
private theorem observed_true (Y₀ Y₁ : Bool → ℝ) :
    observed {true} Y₀ Y₁ true = Y₁ true := by
  simp [observed]

/-- Observed outcome on the comparison unit equals the untreated path. -/
private theorem observed_false (Y₀ Y₁ : Bool → ℝ) :
    observed {true} Y₀ Y₁ false = Y₀ false := by
  simp [observed]

/-- Dirac at `true` gives `{true}` probability one. -/
private theorem dirac_true_singleton_true :
    (Measure.dirac true : Measure Bool) {true} = 1 := by simp

/-- Dirac at `true` gives `{false}` probability zero. -/
private theorem dirac_true_singleton_false :
    (Measure.dirac true : Measure Bool) {false} = 0 := by simp

/-- Conditioning Dirac at `true` on `{true}` is itself. -/
private theorem dirac_cond_true :
    (Measure.dirac true : Measure Bool)[|{true}] = Measure.dirac true := by
  ext s
  simp only [ProbabilityTheory.cond, dirac_true_singleton_true, inv_one,
    one_smul]
  by_cases h : (true : Bool) ∈ s <;> simp [h]

/-- Conditioning Dirac at `true` on the empty cell gives zero. -/
private theorem dirac_cond_compl_zero :
    (Measure.dirac true : Measure Bool)[|({true} : Set Bool)ᶜ] = 0 := by
  apply ProbabilityTheory.cond_eq_zero_of_meas_eq_zero
  simp

/-- Any two-level outcome is integrable against a finite `Bool` measure. -/
private theorem integrable_g (a b : ℝ) (μ : Measure Bool)
    [IsFiniteMeasure μ] : Integrable (g a b) μ := by
  refine Integrable.of_bound
    (measurable_of_countable (g a b)).aestronglyMeasurable
    (‖a‖ + ‖b‖ + 1) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have h1 : g a b ω = a ∨ g a b ω = b := by
    cases ω <;> simp [g]
  cases h1 with
  | inl h =>
    rw [h]
    have hb : (0 : ℝ) ≤ ‖b‖ := norm_nonneg _
    linarith
  | inr h =>
    rw [h]
    have ha : (0 : ℝ) ≤ ‖a‖ := norm_nonneg _
    linarith

/-- T1 untreated path: selection on levels, common trend. -/
def t1_Y0 : ℕ → Bool → ℝ
  | 1 => g 5 1
  | 2 => g 7 3
  | _ => g 0 0

/-- T1 treated path: effect 3 on the treated unit. -/
def t1_Y1 : ℕ → Bool → ℝ
  | 1 => g 5 1
  | 2 => g 10 6
  | _ => g 0 0

/-- T1 no anticipation. -/
theorem t1_noAnticipation :
    ∀ ω ∈ ({true} : Set Bool), t1_Y1 1 ω = t1_Y0 1 ω := by
  intro ω h
  simp [t1_Y1, t1_Y0]

/-- T1 parallel trends holds (2 = 2). -/
theorem t1_parallelTrends :
    ∫ ω, t1_Y0 2 ω - t1_Y0 1 ω ∂coin[|{true}]
      = ∫ ω, t1_Y0 2 ω - t1_Y0 1 ω ∂coin[|({true} : Set Bool)ᶜ] := by
  rw [coin_cond_true, compl_true, coin_cond_false, integral_dirac,
    integral_dirac]
  simp [t1_Y0, g]
  norm_num

/-- T1 ATT equals 3. -/
theorem t1_att_eq_three :
    ∫ ω, t1_Y1 2 ω - t1_Y0 2 ω ∂coin[|{true}] = 3 := by
  rw [coin_cond_true, integral_dirac]
  simp [t1_Y1, t1_Y0, g]
  norm_num

/-- T1 DiD contrast equals 3. -/
theorem t1_did_eq_three :
    (∫ ω, observed {true} (t1_Y0 2) (t1_Y1 2) ω -
      observed {true} (t1_Y0 1) (t1_Y1 1) ω ∂coin[|{true}] -
     ∫ ω, observed {true} (t1_Y0 2) (t1_Y1 2) ω -
      observed {true} (t1_Y0 1) (t1_Y1 1) ω ∂coin[|({true} : Set Bool)ᶜ])
      = 3 := by
  rw [coin_cond_true, compl_true, coin_cond_false, integral_dirac,
    integral_dirac]
  simp [observed_true, observed_false, t1_Y0, t1_Y1, g]
  norm_num

/-- T1 identification via the main theorem. -/
theorem t1_identifies :
    ∫ ω, t1_Y1 2 ω - t1_Y0 2 ω ∂coin[|{true}]
      = (∫ ω, observed {true} (t1_Y0 2) (t1_Y1 2) ω -
        observed {true} (t1_Y0 1) (t1_Y1 1) ω ∂coin[|{true}] -
       ∫ ω, observed {true} (t1_Y0 2) (t1_Y1 2) ω -
        observed {true} (t1_Y0 1) (t1_Y1 1) ω ∂coin[|({true} : Set Bool)ᶜ]) := by
  have hT : MeasurableSet ({true} : Set Bool) := by simp
  have hpos : coin {true} ≠ 0 := by
    rw [coin_apply_singleton]
    exact enn_inv_two_ne_zero
  have hY₀₁ : Integrable (t1_Y0 1) coin := by
    have e : t1_Y0 1 = g 5 1 := rfl
    rw [e]
    exact integrable_g 5 1 coin
  have hY₀₂ : Integrable (t1_Y0 2) coin := by
    have e : t1_Y0 2 = g 7 3 := rfl
    rw [e]
    exact integrable_g 7 3 coin
  have hY₁₂T : Integrable (t1_Y1 2) coin[|{true}] := by
    rw [coin_cond_true]
    have e : t1_Y1 2 = g 10 6 := rfl
    rw [e]
    exact integrable_g 10 6 _
  exact att_eq_diffInDiff hT hpos hY₀₁ hY₀₂ hY₁₂T
    t1_noAnticipation t1_parallelTrends

/-- T1' untreated path. -/
def t1p_Y0 : ℕ → Bool → ℝ
  | 1 => g 0 0
  | 2 => g 1 0
  | _ => g 0 0

/-- T1' treated path. -/
def t1p_Y1 : ℕ → Bool → ℝ
  | 1 => g 0 0
  | 2 => g 3 0
  | _ => g 0 0

/-- T1' no anticipation. -/
theorem t1p_noAnticipation :
    ∀ ω ∈ ({true} : Set Bool), t1p_Y1 1 ω = t1p_Y0 1 ω := by
  intro ω h
  simp [t1p_Y1, t1p_Y0]

/-- T1' ATT equals 2. -/
theorem t1p_att_eq_two :
    ∫ ω, t1p_Y1 2 ω - t1p_Y0 2 ω
      ∂(Measure.dirac true : Measure Bool)[|{true}] = 2 := by
  rw [dirac_cond_true, integral_dirac]
  simp [t1p_Y1, t1p_Y0, g]
  norm_num

/-- T1' DiD contrast equals 3 (junk comparison mean). -/
theorem t1p_did_eq_three :
    (∫ ω, observed {true} (t1p_Y0 2) (t1p_Y1 2) ω -
      observed {true} (t1p_Y0 1) (t1p_Y1 1) ω
      ∂(Measure.dirac true : Measure Bool)[|{true}] -
     ∫ ω, observed {true} (t1p_Y0 2) (t1p_Y1 2) ω -
      observed {true} (t1p_Y0 1) (t1p_Y1 1) ω
      ∂(Measure.dirac true : Measure Bool)[|({true} : Set Bool)ᶜ]) = 3 := by
  rw [dirac_cond_true, dirac_cond_compl_zero, integral_dirac,
    integral_zero_measure]
  simp [observed_true, t1p_Y0, t1p_Y1, g]

/-- T1' DiD differs from the ATT because parallel trends fails there, not
because the comparison group is empty. -/
theorem t1p_did_ne_att :
    (∫ ω, observed {true} (t1p_Y0 2) (t1p_Y1 2) ω -
      observed {true} (t1p_Y0 1) (t1p_Y1 1) ω
      ∂(Measure.dirac true : Measure Bool)[|{true}] -
     ∫ ω, observed {true} (t1p_Y0 2) (t1p_Y1 2) ω -
      observed {true} (t1p_Y0 1) (t1p_Y1 1) ω
      ∂(Measure.dirac true : Measure Bool)[|({true} : Set Bool)ᶜ])
      ≠ ∫ ω, t1p_Y1 2 ω - t1p_Y0 2 ω
        ∂(Measure.dirac true : Measure Bool)[|{true}] := by
  rw [t1p_did_eq_three, t1p_att_eq_two]
  norm_num

/-- T1' parallel trends fails (1 versus 0). -/
theorem t1p_parallelTrends :
    ∫ ω, t1p_Y0 2 ω - t1p_Y0 1 ω
        ∂(Measure.dirac true : Measure Bool)[|{true}] = 1 ∧
      ∫ ω, t1p_Y0 2 ω - t1p_Y0 1 ω
        ∂(Measure.dirac true : Measure Bool)[|({true} : Set Bool)ᶜ] = 0 ∧
      ∫ ω, t1p_Y0 2 ω - t1p_Y0 1 ω
          ∂(Measure.dirac true : Measure Bool)[|{true}]
        ≠ ∫ ω, t1p_Y0 2 ω - t1p_Y0 1 ω
          ∂(Measure.dirac true : Measure Bool)[|({true} : Set Bool)ᶜ] := by
  have h1 : ∫ ω, t1p_Y0 2 ω - t1p_Y0 1 ω
      ∂(Measure.dirac true : Measure Bool)[|{true}] = 1 := by
    rw [dirac_cond_true, integral_dirac]
    simp [t1p_Y0, g]
  have h2 : ∫ ω, t1p_Y0 2 ω - t1p_Y0 1 ω
      ∂(Measure.dirac true : Measure Bool)[|({true} : Set Bool)ᶜ] = 0 := by
    rw [dirac_cond_compl_zero, integral_zero_measure]
  exact ⟨h1, h2, by rw [h1, h2]; norm_num⟩

/-- T2 untreated path: future confounding. -/
def t2_Y0 : ℕ → Bool → ℝ
  | 0 => g 0 0
  | 1 => g 1 1
  | 2 => g 3 2
  | _ => g 0 0

/-- T2 treated path. -/
def t2_Y1 : ℕ → Bool → ℝ
  | 0 => g 0 0
  | 1 => g 1 1
  | 2 => g 4 2
  | _ => g 0 0

/-- T2 pre-trend contrast between periods 0 and 1 is zero. -/
theorem t2_pretrend_eq_zero :
    (∫ ω, observed {true} (t2_Y0 1) (t2_Y1 1) ω -
      observed {true} (t2_Y0 0) (t2_Y1 0) ω ∂coin[|{true}] -
     ∫ ω, observed {true} (t2_Y0 1) (t2_Y1 1) ω -
      observed {true} (t2_Y0 0) (t2_Y1 0) ω ∂coin[|({true} : Set Bool)ᶜ])
      = 0 := by
  rw [coin_cond_true, compl_true, coin_cond_false, integral_dirac,
    integral_dirac]
  simp [observed_true, observed_false, t2_Y0, t2_Y1, g]

/-- T2 no anticipation at period 0. -/
theorem t2_noAnticipation_zero :
    ∀ ω ∈ ({true} : Set Bool), t2_Y1 0 ω = t2_Y0 0 ω := by
  intro ω h
  simp [t2_Y1, t2_Y0]

/-- T2 no anticipation at period 1. -/
theorem t2_noAnticipation_one :
    ∀ ω ∈ ({true} : Set Bool), t2_Y1 1 ω = t2_Y0 1 ω := by
  intro ω h
  simp [t2_Y1, t2_Y0]

/-- T2 parallel trends between 1 and 2 fails (2 versus 1). -/
theorem t2_parallelTrends :
    ∫ ω, t2_Y0 2 ω - t2_Y0 1 ω ∂coin[|{true}] = 2 ∧
      ∫ ω, t2_Y0 2 ω - t2_Y0 1 ω ∂coin[|({true} : Set Bool)ᶜ] = 1 ∧
      ∫ ω, t2_Y0 2 ω - t2_Y0 1 ω ∂coin[|{true}]
        ≠ ∫ ω, t2_Y0 2 ω - t2_Y0 1 ω ∂coin[|({true} : Set Bool)ᶜ] := by
  have h1 : ∫ ω, t2_Y0 2 ω - t2_Y0 1 ω ∂coin[|{true}] = 2 := by
    rw [coin_cond_true, integral_dirac]
    simp [t2_Y0, g]
    norm_num
  have h2 : ∫ ω, t2_Y0 2 ω - t2_Y0 1 ω
      ∂coin[|({true} : Set Bool)ᶜ] = 1 := by
    rw [compl_true, coin_cond_false, integral_dirac]
    simp [t2_Y0, g]
    norm_num
  exact ⟨h1, h2, by rw [h1, h2]; norm_num⟩

/-- T2 DiD contrast equals 2. -/
theorem t2_did_eq_two :
    (∫ ω, observed {true} (t2_Y0 2) (t2_Y1 2) ω -
      observed {true} (t2_Y0 1) (t2_Y1 1) ω ∂coin[|{true}] -
     ∫ ω, observed {true} (t2_Y0 2) (t2_Y1 2) ω -
      observed {true} (t2_Y0 1) (t2_Y1 1) ω ∂coin[|({true} : Set Bool)ᶜ])
      = 2 := by
  rw [coin_cond_true, compl_true, coin_cond_false, integral_dirac,
    integral_dirac]
  simp [observed_true, observed_false, t2_Y0, t2_Y1, g]
  norm_num

/-- T2 ATT equals 1. -/
theorem t2_att_eq_one :
    ∫ ω, t2_Y1 2 ω - t2_Y0 2 ω ∂coin[|{true}] = 1 := by
  rw [coin_cond_true, integral_dirac]
  simp [t2_Y1, t2_Y0, g]
  norm_num

/-- T2 DiD differs from the ATT. -/
theorem t2_did_ne_att :
    (∫ ω, observed {true} (t2_Y0 2) (t2_Y1 2) ω -
      observed {true} (t2_Y0 1) (t2_Y1 1) ω ∂coin[|{true}] -
     ∫ ω, observed {true} (t2_Y0 2) (t2_Y1 2) ω -
      observed {true} (t2_Y0 1) (t2_Y1 1) ω ∂coin[|({true} : Set Bool)ᶜ])
      ≠ ∫ ω, t2_Y1 2 ω - t2_Y0 2 ω ∂coin[|{true}] := by
  rw [t2_did_eq_two, t2_att_eq_one]
  norm_num

/-- T3 untreated path in levels. -/
def t3_Y0 : ℕ → Bool → ℝ
  | 1 => g 1 2
  | 2 => g 2 3
  | _ => g 0 0

/-- T3 treated path in levels. -/
def t3_Y1 : ℕ → Bool → ℝ
  | 1 => g 1 2
  | 2 => g 4 3
  | _ => g 0 0

/-- T3 untreated path in logs. -/
noncomputable def t3log_Y0 : ℕ → Bool → ℝ :=
  fun t ω => Real.log (t3_Y0 t ω)

/-- T3 treated path in logs. -/
noncomputable def t3log_Y1 : ℕ → Bool → ℝ :=
  fun t ω => Real.log (t3_Y1 t ω)

/-- T3 levels no anticipation. -/
theorem t3_levels_noAnticipation :
    ∀ ω ∈ ({true} : Set Bool), t3_Y1 1 ω = t3_Y0 1 ω := by
  intro ω h
  simp [t3_Y1, t3_Y0]

/-- T3 levels parallel trends holds (1 = 1). -/
theorem t3_levels_parallelTrends :
    ∫ ω, t3_Y0 2 ω - t3_Y0 1 ω ∂coin[|{true}]
      = ∫ ω, t3_Y0 2 ω - t3_Y0 1 ω ∂coin[|({true} : Set Bool)ᶜ] := by
  rw [coin_cond_true, compl_true, coin_cond_false, integral_dirac,
    integral_dirac]
  simp [t3_Y0, g]
  norm_num

/-- T3 levels ATT equals 2. -/
theorem t3_levels_att_eq_two :
    ∫ ω, t3_Y1 2 ω - t3_Y0 2 ω ∂coin[|{true}] = 2 := by
  rw [coin_cond_true, integral_dirac]
  simp [t3_Y1, t3_Y0, g]
  norm_num

/-- T3 levels DiD contrast equals 2. -/
theorem t3_levels_did_eq_two :
    (∫ ω, observed {true} (t3_Y0 2) (t3_Y1 2) ω -
      observed {true} (t3_Y0 1) (t3_Y1 1) ω ∂coin[|{true}] -
     ∫ ω, observed {true} (t3_Y0 2) (t3_Y1 2) ω -
      observed {true} (t3_Y0 1) (t3_Y1 1) ω ∂coin[|({true} : Set Bool)ᶜ])
      = 2 := by
  rw [coin_cond_true, compl_true, coin_cond_false, integral_dirac,
    integral_dirac]
  simp [observed_true, observed_false, t3_Y0, t3_Y1, g]
  norm_num

/-- T3 levels identification via the main theorem. -/
theorem t3_levels_identifies :
    ∫ ω, t3_Y1 2 ω - t3_Y0 2 ω ∂coin[|{true}]
      = (∫ ω, observed {true} (t3_Y0 2) (t3_Y1 2) ω -
        observed {true} (t3_Y0 1) (t3_Y1 1) ω ∂coin[|{true}] -
       ∫ ω, observed {true} (t3_Y0 2) (t3_Y1 2) ω -
        observed {true} (t3_Y0 1) (t3_Y1 1) ω ∂coin[|({true} : Set Bool)ᶜ]) := by
  have hT : MeasurableSet ({true} : Set Bool) := by simp
  have hpos : coin {true} ≠ 0 := by
    rw [coin_apply_singleton]
    exact enn_inv_two_ne_zero
  have hY₀₁ : Integrable (t3_Y0 1) coin := by
    have e : t3_Y0 1 = g 1 2 := rfl
    rw [e]
    exact integrable_g 1 2 coin
  have hY₀₂ : Integrable (t3_Y0 2) coin := by
    have e : t3_Y0 2 = g 2 3 := rfl
    rw [e]
    exact integrable_g 2 3 coin
  have hY₁₂T : Integrable (t3_Y1 2) coin[|{true}] := by
    rw [coin_cond_true]
    have e : t3_Y1 2 = g 4 3 := rfl
    rw [e]
    exact integrable_g 4 3 _
  exact att_eq_diffInDiff hT hpos hY₀₁ hY₀₂ hY₁₂T
    t3_levels_noAnticipation t3_levels_parallelTrends

/-- T3 logs parallel trends fails. -/
theorem t3_log_parallelTrends :
    ∫ ω, t3log_Y0 2 ω - t3log_Y0 1 ω ∂coin[|{true}]
        = Real.log 2 - Real.log 1 ∧
      ∫ ω, t3log_Y0 2 ω - t3log_Y0 1 ω ∂coin[|({true} : Set Bool)ᶜ]
        = Real.log 3 - Real.log 2 ∧
      ∫ ω, t3log_Y0 2 ω - t3log_Y0 1 ω ∂coin[|{true}]
        ≠ ∫ ω, t3log_Y0 2 ω - t3log_Y0 1 ω
          ∂coin[|({true} : Set Bool)ᶜ] := by
  have h1 : ∫ ω, t3log_Y0 2 ω - t3log_Y0 1 ω ∂coin[|{true}]
      = Real.log 2 - Real.log 1 := by
    rw [coin_cond_true, integral_dirac]
    simp [t3log_Y0, t3_Y0, g]
  have h2 : ∫ ω, t3log_Y0 2 ω - t3log_Y0 1 ω
      ∂coin[|({true} : Set Bool)ᶜ] = Real.log 3 - Real.log 2 := by
    rw [compl_true, coin_cond_false, integral_dirac]
    simp [t3log_Y0, t3_Y0, g]
  have hne : (Real.log 2 - Real.log 1) ≠ (Real.log 3 - Real.log 2) := by
    have hlog1 : Real.log 1 = 0 := Real.log_one
    have h4eq : (4 : ℝ) = 2 * 2 := by norm_num
    have h4 : Real.log 4 = Real.log 2 + Real.log 2 := by
      rw [h4eq, Real.log_mul (by norm_num) (by norm_num)]
    have hlt : Real.log 3 < Real.log 4 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    have h43 : Real.log 4 ≠ Real.log 3 := ne_of_gt hlt
    intro heq
    rw [hlog1, sub_zero] at heq
    have hsum : Real.log 2 + Real.log 2 = Real.log 3 := by linarith
    rw [← h4] at hsum
    exact h43 hsum
  exact ⟨h1, h2, by rw [h1, h2]; exact hne⟩

/-- T3 logs ATT equals `log 2`. -/
theorem t3_log_att_eq_log_two :
    ∫ ω, t3log_Y1 2 ω - t3log_Y0 2 ω ∂coin[|{true}]
      = Real.log 2 := by
  rw [coin_cond_true, integral_dirac]
  simp only [t3log_Y1, t3log_Y0, t3_Y1, t3_Y0, g, ite_true]
  have h4eq : (4 : ℝ) = 2 * 2 := by norm_num
  have h4 : Real.log 4 = Real.log 2 + Real.log 2 := by
    rw [h4eq, Real.log_mul (by norm_num) (by norm_num)]
  rw [h4]
  ring

/-- T3 logs DiD contrast equals `log (8/3)`. -/
theorem t3_log_did_eq_log_eight_div_three :
    (∫ ω, observed {true} (t3log_Y0 2) (t3log_Y1 2) ω -
      observed {true} (t3log_Y0 1) (t3log_Y1 1) ω ∂coin[|{true}] -
     ∫ ω, observed {true} (t3log_Y0 2) (t3log_Y1 2) ω -
      observed {true} (t3log_Y0 1) (t3log_Y1 1) ω ∂coin[|({true} : Set Bool)ᶜ])
      = Real.log (8 / 3) := by
  rw [coin_cond_true, compl_true, coin_cond_false, integral_dirac,
    integral_dirac]
  simp only [observed_true, observed_false, t3log_Y0, t3log_Y1, t3_Y0,
    t3_Y1, g, ite_true, Bool.false_eq_true, ite_false]
  have hlog1 : Real.log 1 = 0 := Real.log_one
  have h8eq : (8 : ℝ) = 4 * 2 := by norm_num
  have h8 : Real.log 8 = Real.log 4 + Real.log 2 := by
    rw [h8eq, Real.log_mul (by norm_num) (by norm_num)]
  have hdiv : Real.log (8 / 3) = Real.log 8 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [hlog1, hdiv, h8]
  ring

/-- T3 logs DiD differs from the ATT. -/
theorem t3_log_did_ne_att :
    (∫ ω, observed {true} (t3log_Y0 2) (t3log_Y1 2) ω -
      observed {true} (t3log_Y0 1) (t3log_Y1 1) ω ∂coin[|{true}] -
     ∫ ω, observed {true} (t3log_Y0 2) (t3log_Y1 2) ω -
      observed {true} (t3log_Y0 1) (t3log_Y1 1) ω ∂coin[|({true} : Set Bool)ᶜ])
      ≠ ∫ ω, t3log_Y1 2 ω - t3log_Y0 2 ω ∂coin[|{true}] := by
  rw [t3_log_did_eq_log_eight_div_three, t3_log_att_eq_log_two]
  intro heq
  have h1 : (0 : ℝ) < 8 / 3 := by norm_num
  have h2 : (0 : ℝ) < 2 := by norm_num
  have e1 := Real.exp_log h1
  have e2 := Real.exp_log h2
  rw [heq] at e1
  rw [e2] at e1
  norm_num at e1

/-- T4 untreated path: common trend of 1. -/
def t4_Y0 : ℕ → Bool → ℝ
  | 1 => g 0 0
  | 2 => g 1 1
  | _ => g 0 0

/-- T4 treated path: anticipation effect 5 in period 1. -/
def t4_Y1 : ℕ → Bool → ℝ
  | 1 => g 5 0
  | 2 => g 3 1
  | _ => g 0 0

/-- T4 parallel trends holds (1 = 1). -/
theorem t4_parallelTrends :
    ∫ ω, t4_Y0 2 ω - t4_Y0 1 ω ∂coin[|{true}]
      = ∫ ω, t4_Y0 2 ω - t4_Y0 1 ω ∂coin[|({true} : Set Bool)ᶜ] := by
  rw [coin_cond_true, compl_true, coin_cond_false, integral_dirac,
    integral_dirac]
  simp [t4_Y0, g]

/-- T4 no anticipation fails on the treated unit. -/
theorem t4_noAnticipation_fails :
    ¬ ∀ ω ∈ ({true} : Set Bool), t4_Y1 1 ω = t4_Y0 1 ω := by
  intro h
  have htrue := h true (by simp)
  simp [t4_Y1, t4_Y0, g] at htrue

/-- T4 ATT equals 2. -/
theorem t4_att_eq_two :
    ∫ ω, t4_Y1 2 ω - t4_Y0 2 ω ∂coin[|{true}] = 2 := by
  rw [coin_cond_true, integral_dirac]
  simp [t4_Y1, t4_Y0, g]
  norm_num

/-- T4 DiD contrast equals -3. -/
theorem t4_did_eq_neg_three :
    (∫ ω, observed {true} (t4_Y0 2) (t4_Y1 2) ω -
      observed {true} (t4_Y0 1) (t4_Y1 1) ω ∂coin[|{true}] -
     ∫ ω, observed {true} (t4_Y0 2) (t4_Y1 2) ω -
      observed {true} (t4_Y0 1) (t4_Y1 1) ω ∂coin[|({true} : Set Bool)ᶜ])
      = -3 := by
  rw [coin_cond_true, compl_true, coin_cond_false, integral_dirac,
    integral_dirac]
  simp [observed_true, observed_false, t4_Y0, t4_Y1, g]
  norm_num

/-- T4 DiD differs from the ATT although parallel trends holds. -/
theorem t4_did_ne_att :
    (∫ ω, observed {true} (t4_Y0 2) (t4_Y1 2) ω -
      observed {true} (t4_Y0 1) (t4_Y1 1) ω ∂coin[|{true}] -
     ∫ ω, observed {true} (t4_Y0 2) (t4_Y1 2) ω -
      observed {true} (t4_Y0 1) (t4_Y1 1) ω ∂coin[|({true} : Set Bool)ᶜ])
      ≠ ∫ ω, t4_Y1 2 ω - t4_Y0 2 ω ∂coin[|{true}] := by
  rw [t4_did_eq_neg_three, t4_att_eq_two]
  norm_num

/-- R1 untreated paths (both zero). -/
def r1_Y0 : ℕ → ℕ → ℝ := fun _ _ => 0

/-- R1 treated path: zero in period 1, growing in period 2. -/
def r1_Y1 : ℕ → ℕ → ℝ
  | 1 => fun _ => 0
  | 2 => fun n => (n : ℝ) + 1
  | _ => fun _ => 0

/-- Counting measure on `ℕ` is not finite. -/
private theorem r1_count_not_finite :
    ¬IsFiniteMeasure (Measure.count : Measure ℕ) := by
  intro hf
  have htop : (Measure.count : Measure ℕ) Set.univ = ⊤ :=
    Measure.count_apply_infinite Set.infinite_univ
  have hlt : (Measure.count : Measure ℕ) Set.univ < ⊤ := hf.1
  exact (ne_of_lt hlt) htop

/-- Constant one is not integrable against counting measure on `ℕ`. -/
private theorem r1_const_one_not_integrable :
    ¬Integrable (fun _ : ℕ => (1 : ℝ)) (Measure.count : Measure ℕ) := by
  rw [integrable_const_iff]
  simp [r1_count_not_finite]

/-- R1 `Y₁ 2` is not globally integrable (heavy control tail). -/
theorem r1_notIntegrable :
    ¬Integrable (r1_Y1 2) (Measure.count : Measure ℕ) := by
  intro h
  have hbound : ∀ᵐ n ∂(Measure.count : Measure ℕ),
      ‖(1 : ℝ)‖ ≤ r1_Y1 2 n := by
    refine Filter.Eventually.of_forall fun n => ?_
    show ‖(1 : ℝ)‖ ≤ ((n : ℝ) + 1)
    rw [norm_one]
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hconst : Integrable (fun _ : ℕ => (1 : ℝ))
      (Measure.count : Measure ℕ) :=
    h.mono' aestronglyMeasurable_const hbound
  exact r1_const_one_not_integrable hconst

/-- Conditioning counting measure on `{0}` gives `dirac 0`. -/
private theorem r1_count_cond_zero :
    (Measure.count : Measure ℕ)[|{0}] = Measure.dirac 0 := by
  ext s
  simp only [ProbabilityTheory.cond, Measure.smul_apply,
    Measure.count_singleton]
  by_cases h : (0 : ℕ) ∈ s <;> simp [h]

/-- R1 `Y₁ 2` is integrable on the treated cell. -/
theorem r1_integrableT :
    Integrable (r1_Y1 2) (Measure.count : Measure ℕ)[|{0}] := by
  rw [r1_count_cond_zero]
  exact integrable_dirac (by simp [r1_Y1])

/-- R1 no anticipation. -/
theorem r1_noAnticipation :
    ∀ ω ∈ ({0} : Set ℕ), r1_Y1 1 ω = r1_Y0 1 ω := by
  intro ω h
  rfl

/-- R1 parallel trends holds (0 = 0). -/
theorem r1_parallelTrends :
    ∫ ω, r1_Y0 2 ω - r1_Y0 1 ω ∂(Measure.count : Measure ℕ)[|{0}]
      = ∫ ω, r1_Y0 2 ω - r1_Y0 1 ω
        ∂(Measure.count : Measure ℕ)[|({0} : Set ℕ)ᶜ] := by
  have h0 : ∀ ω : ℕ, r1_Y0 2 ω - r1_Y0 1 ω = 0 := fun ω => by
    have e1 : r1_Y0 2 ω = (0 : ℝ) := rfl
    have e2 : r1_Y0 1 ω = (0 : ℝ) := rfl
    rw [e1, e2, sub_self]
  have hT : ∫ ω, r1_Y0 2 ω - r1_Y0 1 ω
      ∂(Measure.count : Measure ℕ)[|{0}] = 0 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall h0), integral_zero]
  have hTc : ∫ ω, r1_Y0 2 ω - r1_Y0 1 ω
      ∂(Measure.count : Measure ℕ)[|({0} : Set ℕ)ᶜ] = 0 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall h0), integral_zero]
  rw [hT, hTc]

/-- R1 treated cell has positive mass. -/
theorem r1_posT : (Measure.count : Measure ℕ) {0} ≠ 0 := by
  rw [Measure.count_singleton]
  simp

/-- R1 comparison cell has positive mass. -/
theorem r1_posTc : (Measure.count : Measure ℕ) ({0} : Set ℕ)ᶜ ≠ 0 := by
  have hsub : ({1} : Set ℕ) ⊆ ({0} : Set ℕ)ᶜ := by
    intro x hx
    simp at hx ⊢
    rw [hx]
    norm_num
  have hle : (Measure.count : Measure ℕ) {1}
      ≤ (Measure.count : Measure ℕ) ({0} : Set ℕ)ᶜ :=
    measure_mono hsub
  rw [Measure.count_singleton] at hle
  intro hz
  rw [hz] at hle
  have h10 : (1 : ENNReal) = 0 := le_antisymm hle zero_le
  exact one_ne_zero h10

/-- R1 identification via the narrowed main theorem. -/
theorem r1_identifies :
    ∫ ω, r1_Y1 2 ω - r1_Y0 2 ω ∂(Measure.count : Measure ℕ)[|{0}]
      = (∫ ω, observed {0} (r1_Y0 2) (r1_Y1 2) ω -
        observed {0} (r1_Y0 1) (r1_Y1 1) ω
        ∂(Measure.count : Measure ℕ)[|{0}] -
       ∫ ω, observed {0} (r1_Y0 2) (r1_Y1 2) ω -
        observed {0} (r1_Y0 1) (r1_Y1 1) ω
        ∂(Measure.count : Measure ℕ)[|({0} : Set ℕ)ᶜ]) := by
  have hT : MeasurableSet ({0} : Set ℕ) := by simp
  have hY₀₁ : Integrable (r1_Y0 1) (Measure.count : Measure ℕ) := by
    have e : r1_Y0 1 = fun _ => (0 : ℝ) := rfl
    rw [e, integrable_const_iff]
    exact Or.inl rfl
  have hY₀₂ : Integrable (r1_Y0 2) (Measure.count : Measure ℕ) := by
    have e : r1_Y0 2 = fun _ => (0 : ℝ) := rfl
    rw [e, integrable_const_iff]
    exact Or.inl rfl
  exact att_eq_diffInDiff hT r1_posT hY₀₁ hY₀₂ r1_integrableT
    r1_noAnticipation r1_parallelTrends

end MathlibExtTest.Probability.Causality.DifferenceInDifferences
