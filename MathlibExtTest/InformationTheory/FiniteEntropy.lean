/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.FiniteEntropy

@[expose] public section

/-!
# Tests for finite entropy, surprisal and cross-entropy
-/

set_option autoImplicit false

open MeasureTheory Real InformationTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.FiniteEntropy

/-- A fair coin. -/
noncomputable def fair : PMF Bool :=
  PMF.ofFintype (fun _ ↦ ((1 / 2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj, add_halves])

/-- A coin biased towards `true` with probability `3 / 4`. -/
noncomputable def biased : PMF Bool :=
  PMF.ofFintype (fun b ↦ ((cond b (3 / 4) (1 / 4) : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, ← ENNReal.coe_add, ← ENNReal.coe_one,
      ENNReal.coe_inj, ← NNReal.coe_inj]
    push_cast
    norm_num)

theorem fair_apply (b : Bool) : (fair b).toReal = 1 / 2 := by
  simp [fair]

/-- A fair coin carries one bit. -/
theorem shannonEntropy_fair : shannonEntropy fair = 1 := by
  rw [shannonEntropy, Fintype.sum_bool, fair_apply, fair_apply]
  simp only [negMulLog, one_div, log_inv]
  field_simp
  ring

/-- An outcome of probability `1 / 2` carries one bit of surprisal. -/
example : surprisal (2⁻¹ : ℝ≥0∞) = 1 := by
  rw [surprisal_of_ne_zero (by simp), ENNReal.toReal_inv, ENNReal.toReal_ofNat, logb, log_inv,
    neg_div, neg_neg, div_self (log_pos one_lt_two).ne', ENNReal.ofReal_one]

/-- An outcome the prediction rules out costs `∞`: predicting `false` with certainty for fair
flips. -/
example : crossEntropy fair (PMF.pure false) = ∞ :=
  crossEntropy_eq_top_iff.mpr ⟨true, by simp, by simp [fair]⟩

/-- An impossible label has infinite log loss. -/
example : crossEntropy (PMF.pure true) (PMF.pure false) = ∞ := by
  rw [crossEntropy_pure]
  simp [surprisal_zero]

/-- Predicting the biased coin for fair flips costs strictly more than one bit. -/
example : ENNReal.ofReal (shannonEntropy fair) < crossEntropy fair biased := by
  refine lt_of_le_of_ne (shannonEntropy_le_crossEntropy fair biased) fun h ↦ ?_
  have := congrArg (fun p : PMF Bool ↦ (p true).toReal)
    ((crossEntropy_eq_shannonEntropy_iff fair biased).mp h.symm)
  simp [fair, biased] at this
  norm_num at this

/-- The divergence of the two coins from Mathlib's `klDiv`, in nats. -/
example : (klDiv fair.toMeasure biased.toMeasure).toReal =
    1 / 2 * log ((1 / 2) / (1 / 4)) + 1 / 2 * log ((1 / 2) / (3 / 4)) := by
  have hpq : ∀ a, biased a = 0 → fair a = 0 := fun a h ↦ by
    cases a <;> simp_all [biased]
  rw [toReal_klDiv_toMeasure hpq, Fintype.sum_bool, fair_apply, fair_apply]
  simp [biased]
  norm_num
  ring

end MathlibExtTest.InformationTheory.FiniteEntropy
