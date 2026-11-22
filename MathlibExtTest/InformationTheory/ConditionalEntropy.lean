/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy

@[expose] public section

/-!
# Tests for finite mutual information and conditional entropy
-/

set_option autoImplicit false

open MeasureTheory Real InformationTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.ConditionalEntropy

/-- Two copies of one fair bit: `X = Y`. -/
noncomputable def copy : PMF (Bool × Bool) :=
  PMF.ofFintype (fun z ↦ if z.1 = z.2 then ((1 / 2 : ℝ≥0) : ℝ≥0∞) else 0) (by
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    simp only [ite_true, Bool.true_eq_false, Bool.false_eq_true, ite_false, add_zero, zero_add]
    rw [← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj, add_halves])

theorem copy_apply (a b : Bool) : (copy (a, b)).toReal = if a = b then 1 / 2 else 0 := by
  by_cases h : a = b <;> simp [copy, h]

theorem shannonEntropy_copy_fst : shannonEntropy (copy.map Prod.fst) = 1 := by
  have h : ∀ a, ((copy.map Prod.fst) a).toReal = 1 / 2 := fun a ↦ by
    rw [toReal_map_fst_apply, Fintype.sum_bool, copy_apply, copy_apply]
    cases a <;> simp
  rw [shannonEntropy, Fintype.sum_bool, h, h]
  simp only [negMulLog, one_div, log_inv]
  field_simp
  ring

theorem shannonEntropy_copy_snd : shannonEntropy (copy.map Prod.snd) = 1 := by
  have h : ∀ b, ((copy.map Prod.snd) b).toReal = 1 / 2 := fun b ↦ by
    rw [toReal_map_snd_apply, Fintype.sum_bool, copy_apply, copy_apply]
    cases b <;> simp
  rw [shannonEntropy, Fintype.sum_bool, h, h]
  simp only [negMulLog, one_div, log_inv]
  field_simp
  ring

theorem shannonEntropy_copy : shannonEntropy copy = 1 := by
  rw [shannonEntropy, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  simp only [copy_apply, ite_true, Bool.true_eq_false, Bool.false_eq_true, ite_false, negMulLog,
    one_div, log_inv]
  field_simp
  ring

/-- Knowing one copy reveals the other: one bit of mutual information. -/
example : measureMutualInformation
    (⟨copy.toMeasure, inferInstance⟩ : ProbabilityMeasure (Bool × Bool)) = 1 := by
  rw [measureMutualInformation_toMeasure, shannonEntropy_copy_fst, shannonEntropy_copy_snd,
    shannonEntropy_copy]
  norm_num

/-- Given one copy, the other carries no information. -/
example : finiteConditionalEntropy copy = 0 := by
  have := shannonEntropy_eq_add_finiteConditionalEntropy copy
  rw [shannonEntropy_copy, shannonEntropy_copy_fst] at this
  linarith

/-- Copies are not independent. -/
example : copy.toMeasure ≠ (copy.map Prod.fst).toMeasure.prod (copy.map Prod.snd).toMeasure := by
  intro h
  have h0 := (measureMutualInformation_toMeasure_eq_zero_iff copy).mpr h
  rw [measureMutualInformation_toMeasure, shannonEntropy_copy_fst, shannonEntropy_copy_snd,
    shannonEntropy_copy] at h0
  norm_num at h0

end MathlibExtTest.InformationTheory.ConditionalEntropy
