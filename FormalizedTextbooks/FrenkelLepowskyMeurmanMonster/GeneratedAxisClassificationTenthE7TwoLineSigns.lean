/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignKernelCount

/-! The complete original Golay signs constant on each of the two actual flag supports. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- The actual code-coordinate conditions for independent unsigned signs on the two lines. -/
def generatedTenthE7TwoLineSignCondition (c : golayCode) : Prop :=
  c.val 16 = c.val 21 ∧ c.val 4 = c.val 7 ∧ c.val 4 = c.val 8 ∧
    c.val 4 = c.val 11 ∧ c.val 4 = c.val 18 ∧ c.val 4 = c.val 20

/-- The complete coordinate conditions have their constructive original-code decision procedure. -/
instance generatedTenthE7TwoLineSignConditionDecidable (c : golayCode) :
    Decidable (generatedTenthE7TwoLineSignCondition c) := by
  unfold generatedTenthE7TwoLineSignCondition
  infer_instance

/-- The entire original Golay-code subset satisfying those complete coordinate conditions. -/
def generatedTenthE7TwoLineSigns := {c : golayCode // generatedTenthE7TwoLineSignCondition c}

/-- All original labels satisfying exactly the same actual code-coordinate conditions. -/
def generatedTenthE7TwoLineSignLabels : Finset (Fin 4096) :=
  Finset.univ.filter fun d => generatedTenthE7TwoLineSignCondition (golayCodeLabelEquiv d)

set_option maxHeartbeats 4000000 in
-- Count every one of the 4096 original encoder words under all six actual equalities.
/-- Exactly 128 original Golay labels are constant separately on both full supports. -/
theorem generatedTenth_e7_two_line_sign_labels_card :
    generatedTenthE7TwoLineSignLabels.card = 128 := by
  unfold generatedTenthE7TwoLineSignLabels generatedTenthE7TwoLineSignCondition
  decide +kernel

/-- The original label bijection identifies the whole actual code subset with its exact filter. -/
def generatedTenthE7TwoLineSignEquiv : generatedTenthE7TwoLineSigns ≃
    generatedTenthE7TwoLineSignLabels where
  toFun c := ⟨golayCodeLabelEquiv.symm c.val, by
    simp only [generatedTenthE7TwoLineSignLabels, Finset.mem_filter, Finset.mem_univ,
      true_and, Equiv.apply_symm_apply]
    exact c.property⟩
  invFun d := ⟨golayCodeLabelEquiv d.val, by
    exact (Finset.mem_filter.mp d.property).2⟩
  left_inv c := by apply Subtype.ext; exact golayCodeLabelEquiv.apply_symm_apply c.val
  right_inv d := by apply Subtype.ext; exact golayCodeLabelEquiv.symm_apply_apply d.val

/-- The whole actual Golay-code subset has 128 elements, without an enumeration premise. -/
theorem generatedTenth_e7_two_line_signs_card : Nat.card generatedTenthE7TwoLineSigns = 128 := by
  rw [Nat.card_congr generatedTenthE7TwoLineSignEquiv]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    generatedTenth_e7_two_line_sign_labels_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
