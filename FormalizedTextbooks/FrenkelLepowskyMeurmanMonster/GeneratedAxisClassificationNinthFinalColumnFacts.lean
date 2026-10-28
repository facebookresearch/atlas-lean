/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthTensorSupportData

/-! Exact candidate-mask algebra isolates one squared coordinate and the detecting support.
These cache facts do not assert their occurrence in the actual Ninth tensor. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem magnitude_bits (p b₁ b₂ b₄ b₈ : Bool) :
    ((if p then (2 : ℤ) else -2) *
      ((if b₁ then (1 : ℤ) else 0) + (if b₂ then 2 else 0) +
        (if b₄ then 4 else 0) + (if b₈ then 8 else 0))) ^ 2 = 324 ↔
      (b₁ && b₈ && !b₂ && !b₄) = true := by
  cases p <;> cases b₁ <;> cases b₂ <;> cases b₄ <;> cases b₈ <;> decide +kernel

/-- A genuine natural-number mask identity isolates the only candidate magnitude eighteen. -/
theorem generatedNinth_final_column_exceptional_mask :
    generatedNinthFinalColumnBit1 &&& generatedNinthFinalColumnBit8 &&&
      (generatedNinthFinalColumnBit2 ^^^ (2 ^ 4096 - 1)) &&&
      (generatedNinthFinalColumnBit4 ^^^ (2 ^ 4096 - 1)) = 2 ^ 1177 := by
  decide +kernel

/-- Every candidate squared coordinate of size324 has the one original source label1177. -/
theorem generatedNinth_final_column_square_iff (n : Fin 4096) :
    (generatedNinthFinalColumnInteger n) ^ 2 = 324 ↔ n.val = 1177 := by
  have he : generatedNinthFinalColumnInteger n =
      (if generatedNinthFinalColumnPositive.testBit n.val then (2 : ℤ) else -2) *
        ((if generatedNinthFinalColumnBit1.testBit n.val then (1 : ℤ) else 0) +
          (if generatedNinthFinalColumnBit2.testBit n.val then 2 else 0) +
          (if generatedNinthFinalColumnBit4.testBit n.val then 4 else 0) +
          (if generatedNinthFinalColumnBit8.testBit n.val then 8 else 0)) := by
    unfold generatedNinthFinalColumnInteger
    split_ifs <;> ring
  rw [he, magnitude_bits]
  have h := congrArg (fun m : ℕ => m.testBit n.val)
    generatedNinth_final_column_exceptional_mask
  have hn : decide (n.val < 4096) = true := by simp only [n.isLt, decide_true]
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow, hn, Bool.xor_true] at h
  rw [h]
  simp only [decide_eq_true_eq]
  exact eq_comm

/-- Every selected detecting label is nonzero in the candidate integer data. -/
theorem generatedNinth_final_column_detecting_nonzero : ∀ i : Fin 13,
    generatedNinthFinalColumnInteger (generatedNinthTensorSupportLabels i) ≠ 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
