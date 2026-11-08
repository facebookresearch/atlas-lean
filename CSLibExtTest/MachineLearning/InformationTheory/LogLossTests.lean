/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.InformationTheory.LogLoss

@[expose] public section

/-!
# Tests for the cross-entropy loss of a classifier
-/

set_option autoImplicit false

open Real InformationTheory Cslib.MachineLearning.InformationTheory
open scoped ENNReal NNReal

namespace CSLibExtTest.MachineLearning.InformationTheory.LogLoss

/-- A classifier that always predicts a fair coin. -/
noncomputable def fair : PMF Bool :=
  PMF.ofFintype (fun _ ↦ ((1 / 2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj, add_halves])

/-- On any two labelled examples, always predicting a fair coin costs exactly one bit per
example. -/
example (D : Fin 2 → Unit × Bool) : crossEntropyLoss (fun _ ↦ fair) D = 1 := by
  have h : ∀ b, surprisal (fair b) = 1 := fun b ↦ by
    simp only [fair, PMF.ofFintype_apply]
    rw [surprisal_of_ne_zero (by simp), ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat, one_div, logb, log_inv, neg_div, neg_neg,
      div_self (log_pos one_lt_two).ne', ENNReal.ofReal_one]
  rw [crossEntropyLoss_eq, Fin.sum_univ_two, h, h, one_add_one_eq_two]
  exact ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top

/-- A classifier that rules out the observed label has infinite loss. -/
example : crossEntropyLoss (fun _ : Unit ↦ PMF.pure false) (fun _ : Fin 1 ↦ ((), true)) = ∞ :=
  (crossEntropyLoss_eq_top_iff _ _ one_ne_zero).mpr ⟨0, by simp⟩

/-- Lower loss means higher likelihood: predicting `true` with certainty beats the fair coin on a
sample of `true` labels. -/
example : crossEntropyLoss (fun _ : Unit ↦ PMF.pure true) (fun _ : Fin 3 ↦ ((), true)) ≤
    crossEntropyLoss (fun _ ↦ fair) (fun _ : Fin 3 ↦ ((), true)) := by
  rw [crossEntropyLoss_le_iff _ _ _ (by norm_num)]
  simp only [PMF.pure_apply, ite_true, ENNReal.toReal_one, Finset.prod_const_one]
  exact Finset.prod_le_one₀ (fun _ _ ↦ ENNReal.toReal_nonneg) fun _ _ ↦ by
    simp only [fair, PMF.ofFintype_apply, ENNReal.coe_toReal]
    norm_num

/-- Zero likelihood: a classifier that rules out an observed label never has loss at most that of
one that does not. -/
example : ¬ crossEntropyLoss (fun _ : Unit ↦ PMF.pure false) (fun _ : Fin 1 ↦ ((), true)) ≤
    crossEntropyLoss (fun _ ↦ fair) (fun _ : Fin 1 ↦ ((), true)) := by
  rw [crossEntropyLoss_le_iff _ _ _ one_ne_zero]
  simp [fair]

/-- Zero likelihood on both sides: both losses are `∞`, so each is at most the other. -/
example : crossEntropyLoss (fun _ : Unit ↦ PMF.pure false) (fun _ : Fin 1 ↦ ((), true)) ≤
    crossEntropyLoss (fun _ : Unit ↦ PMF.pure false) (fun _ : Fin 1 ↦ ((), true)) := by
  rw [crossEntropyLoss_le_iff _ _ _ one_ne_zero]

end CSLibExtTest.MachineLearning.InformationTheory.LogLoss
