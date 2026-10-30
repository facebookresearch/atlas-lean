/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.InformationTheory.InformationGain

@[expose] public section

/-!
# Tests for information gain
-/

set_option autoImplicit false

open MeasureTheory Real InformationTheory Cslib.MachineLearning.InformationTheory
open scoped ENNReal NNReal

namespace CSLibExtTest.MachineLearning.InformationTheory.InformationGain

/-- An attribute that determines the label: the label copies a fair bit. -/
noncomputable def copy : PMF (Bool × Bool) :=
  PMF.ofFintype (fun z ↦ if z.1 = z.2 then ((1 / 2 : ℝ≥0) : ℝ≥0∞) else 0) (by
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    simp only [ite_true, Bool.true_eq_false, Bool.false_eq_true, ite_false, add_zero, zero_add]
    rw [← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj, add_halves])

theorem copy_apply (a b : Bool) : (copy (a, b)).toReal = if a = b then 1 / 2 else 0 := by
  by_cases h : a = b <;> simp [copy, h]

theorem entropy_half : negMulLog (1 / 2) + negMulLog (1 / 2) = log 2 := by
  simp only [negMulLog, one_div, log_inv]
  ring

/-- Splitting on an attribute that determines a fair label gains one full bit. -/
example : infoGain copy = 1 := by
  have hX : ∀ a, ((copy.map Prod.fst) a).toReal = 1 / 2 := fun a ↦ by
    rw [toReal_map_fst_apply, Fintype.sum_bool, copy_apply, copy_apply]
    cases a <;> simp
  have hY : ∀ b, ((copy.map Prod.snd) b).toReal = 1 / 2 := fun b ↦ by
    rw [toReal_map_snd_apply, Fintype.sum_bool, copy_apply, copy_apply]
    cases b <;> simp
  rw [infoGain_eq, shannonEntropy, shannonEntropy, shannonEntropy, Fintype.sum_bool,
    Fintype.sum_bool, hX, hX, hY, hY, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool]
  simp only [copy_apply, ite_true, Bool.true_eq_false, Bool.false_eq_true, ite_false,
    negMulLog_zero, add_zero, zero_add, entropy_half]
  field_simp
  norm_num

/-- An informative split is not independent of the label. -/
example : copy.toMeasure ≠ (copy.map Prod.fst).toMeasure.prod (copy.map Prod.snd).toMeasure := by
  intro h
  have h0 := (infoGain_eq_zero_iff copy).mpr h
  have h1 : infoGain copy = 1 := by
    have hX : ∀ a, ((copy.map Prod.fst) a).toReal = 1 / 2 := fun a ↦ by
      rw [toReal_map_fst_apply, Fintype.sum_bool, copy_apply, copy_apply]
      cases a <;> simp
    have hY : ∀ b, ((copy.map Prod.snd) b).toReal = 1 / 2 := fun b ↦ by
      rw [toReal_map_snd_apply, Fintype.sum_bool, copy_apply, copy_apply]
      cases b <;> simp
    rw [infoGain_eq, shannonEntropy, shannonEntropy, shannonEntropy, Fintype.sum_bool,
      Fintype.sum_bool, hX, hX, hY, hY, Fintype.sum_prod_type, Fintype.sum_bool,
      Fintype.sum_bool, Fintype.sum_bool]
    simp only [copy_apply, ite_true, Bool.true_eq_false, Bool.false_eq_true, ite_false,
      negMulLog_zero, add_zero, zero_add, entropy_half]
    field_simp
    norm_num
  linarith

/-- Information gain is never negative. -/
example (p : PMF (Bool × Bool)) : 0 ≤ infoGain p := infoGain_nonneg p

end CSLibExtTest.MachineLearning.InformationTheory.InformationGain
