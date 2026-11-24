/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.WaldInequalities
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Tests for Wald's inequalities

A non-degenerate instance: observations with values in `Bool`, `P₀` the fair coin and `P₁` the
coin with `P₁ {true} = 1/3`. The two laws are distinct and mutually absolutely continuous, so
Wald's inequalities apply.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.WaldInequalities

/-- Two laws on a finite type with full support are absolutely continuous. -/
theorem ofFintype_absolutelyContinuous {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {f g : α → ℝ≥0∞} (hf : ∑ a, f a = 1) (hg : ∑ a, g a = 1)
    (hf0 : ∀ a, f a ≠ 0) (hg0 : ∀ a, g a ≠ 0) :
    (PMF.ofFintype f hf).toMeasure ≪ (PMF.ofFintype g hg).toMeasure := by
  have hsupp : ∀ {h : α → ℝ≥0∞} (hh : ∑ a, h a = 1), (∀ a, h a ≠ 0) →
      (PMF.ofFintype h hh).support = Set.univ := fun hh h0 => by
    rw [PMF.support_ofFintype]; ext a; simp [h0 a]
  intro s hs
  have hsm : MeasurableSet s := s.toFinite.measurableSet
  rw [(PMF.ofFintype g hg).toMeasure_apply_eq_zero_iff hsm, hsupp hg hg0] at hs
  rw [(PMF.ofFintype f hf).toMeasure_apply_eq_zero_iff hsm, hsupp hf hf0]
  exact hs

/-- The fair coin. -/
noncomputable def fairCoin : Measure Bool :=
  (PMF.ofFintype (fun _ => 2⁻¹) (by
    simp only [Fintype.sum_bool]; exact ENNReal.inv_two_add_inv_two)).toMeasure

theorem sum_biased : ∑ b : Bool, (if b then (3 : ℝ≥0∞)⁻¹ else 2 * 3⁻¹) = 1 := by
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  rw [← one_add_mul, show (1 : ℝ≥0∞) + 2 = 3 by norm_num,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

/-- The coin with `P {true} = 1/3`. -/
noncomputable def biasedCoin : Measure Bool :=
  (PMF.ofFintype (fun b => if b then (3 : ℝ≥0∞)⁻¹ else 2 * 3⁻¹) sum_biased).toMeasure

instance : IsProbabilityMeasure fairCoin := by unfold fairCoin; infer_instance
instance : IsProbabilityMeasure biasedCoin := by unfold biasedCoin; infer_instance

theorem biasedCoin_ac : biasedCoin ≪ fairCoin :=
  ofFintype_absolutelyContinuous _ _ (fun b => by cases b <;> simp) (fun _ => by simp)

theorem fairCoin_ac : fairCoin ≪ biasedCoin :=
  ofFintype_absolutelyContinuous _ _ (fun _ => by simp) (fun b => by cases b <;> simp)

/-- The two coins are distinct laws, so the instance is not degenerate. -/
theorem fairCoin_ne_biasedCoin : fairCoin ≠ biasedCoin := by
  intro h
  have := congrArg (fun μ : Measure Bool => μ {true}) h
  simp only [fairCoin, biasedCoin, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.ofFintype_apply, ite_true] at this
  exact absurd (inv_injective this) (by norm_num)

/-- Wald's two inequalities for the fair coin against the biased coin. -/
example (a b : ℝ) :
    Measure.infinitePi (fun _ : ℕ => biasedCoin)
        (sprtAcceptZero fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b) ≤
        ENNReal.ofReal (Real.exp a) * Measure.infinitePi (fun _ : ℕ => fairCoin)
          (sprtAcceptZero fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b) ∧
      ENNReal.ofReal (Real.exp b) * Measure.infinitePi (fun _ : ℕ => fairCoin)
          (sprtAcceptOne fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b) ≤
        Measure.infinitePi (fun _ : ℕ => biasedCoin)
          (sprtAcceptOne fairCoin biasedCoin biasedCoin_ac fairCoin_ac a b) :=
  ⟨sprt_acceptZero_le biasedCoin_ac fairCoin_ac a b,
    sprt_acceptOne_ge biasedCoin_ac fairCoin_ac a b⟩

/-- The likelihood-ratio statistics admit only mutually absolutely continuous laws. The fair
coin is not absolutely continuous with respect to the coin that always shows `true`: under the
second law `false` is impossible, its log-likelihood ratio against the fair coin is `-∞`, and the
real-valued `llr` would read it as `0`. -/
example : ¬ fairCoin ≪ Measure.dirac true := by
  intro h
  have h0 := h (s := {false}) (by simp)
  simp [fairCoin, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h0

end MathlibExtTest.Probability.Statistics.WaldInequalities
