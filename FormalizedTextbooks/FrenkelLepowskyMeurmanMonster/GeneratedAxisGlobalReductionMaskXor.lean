/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskRows

/-! Exact column-XOR evaluation commutes with mask addition. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Direct indexed column evaluation is genuinely linear for exact bitwise mask addition. -/
theorem generatedAxisGlobalMaskRowsAction_xor (rows : List (ℕ × ℕ)) (a b : ℕ) :
    generatedAxisGlobalMaskRowsAction rows (a ^^^ b) =
      generatedAxisGlobalMaskRowsAction rows a ^^^ generatedAxisGlobalMaskRowsAction rows b := by
  induction rows with
  | nil => simp [generatedAxisGlobalMaskRowsAction]
  | cons p rows ih =>
      rcases p with ⟨i, c⟩
      cases ha : a.testBit i <;> cases hb : b.testBit i
      · simp only [generatedAxisGlobalMaskRowsAction, Nat.testBit_xor, ha, hb,
          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact ih
      · simp only [generatedAxisGlobalMaskRowsAction, Nat.testBit_xor, ha, hb,
          Bool.bne_true, Bool.not_false, ↓reduceIte, Nat.xor_eq, Bool.false_eq_true]
        rw [ih, Nat.xor_left_comm]
      · simp only [generatedAxisGlobalMaskRowsAction, Nat.testBit_xor, ha, hb,
          Bool.bne_false, ↓reduceIte, Nat.xor_eq, Bool.false_eq_true]
        rw [ih, Nat.xor_assoc]
      · simp only [generatedAxisGlobalMaskRowsAction, Nat.testBit_xor, ha, hb,
          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Nat.xor_eq]
        rw [ih]
        have hx : (c ^^^ generatedAxisGlobalMaskRowsAction rows a) ^^^
            (c ^^^ generatedAxisGlobalMaskRowsAction rows b) =
            generatedAxisGlobalMaskRowsAction rows a ^^^
              generatedAxisGlobalMaskRowsAction rows b := by
          calc
            _ = (c ^^^ c) ^^^ (generatedAxisGlobalMaskRowsAction rows a ^^^
              generatedAxisGlobalMaskRowsAction rows b) := by ac_rfl
            _ = _ := by simp
        exact hx.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
